# Created on June, 2022
# author: AllanEduardo42
# This code is an adaptation of that found in:
# https://en.wikiversity.org/wiki/Reed%E2%80%93Solomon_codes_for_coders

# ======================================================
#           Reed Solomon coding and decoding
# ======================================================

using OffsetArrays

struct ReedSolomonError <: Exception
    msg::AbstractString
end

function gf_mult_noLUT(x, y, prim=0)
#'''Multiplication in Galois Fields without using a precomputed look-up table
#   (and thus it's slower) by using the standard carry-less multiplication + 
#   modular reduction using an irreducible prime polynomial.'''
    
    ### Define bitwise carry-less operations as inner functions ### 

    function cl_mult(x, y)
    #'''Bitwise carry-less multiplication on integers.'''

        z = 0x0000
        x = UInt16(x)
        y = UInt16(y) 
        i = 0
        while (y >> i) > 0 # while there are '1' bits. The operator '>>' shifts
                           # the bit string to the right, in fact getting rid of
                           # the least significative bits. The number of right
                           # shifts is given right after the operator; e.g.:
                           # 0b01010101 >> 1 = 0b0101010. The ''while'' loop stops
                           # when there are no '1' bits left.
            if y & (1 << i) > 0 # if the ith bit of y from left to right is '1'.
                                # The operator '<<' shifts the bit string to the
                                # left, in fact inserting zeros to the right. The
                                # number of zeros is given right after the operator.
                                # e.g.: 0b00000001 << 2 = 0b00000100. The condition
                                # represent a search for '1' bits of y.
                z ⊻= x << i # when the ith bit of y is '1', we sum x in the result
                            # i bits shifted to the left. 
            end
            i += 1
        end
        return z
    end


    function cl_div(dividend, divisor)
    #'''Bitwise carry-less long division on integers and returns the remainder.'''

        # Compute the position of the most significant bit for each integers
        dl1 = bit_length(dividend)
        dl2 = bit_length(divisor)
        # If the dividend is smaller than the divisor, just exit
        if dl1 < dl2
            return dividend
        end
        # Else, align the most significant 1 of the divisor to the most significant
    # 1 of the dividend (by shifting the divisor)
        for i in range(dl1-dl2,stop=0,step=-1)
            # Check that the dividend is divisible (useless for the first iteration
        # but important for the next ones)
            if (dividend & (1 << (i+dl2-1))) > 0
                # If divisible, then shift the divisor to align the most significant
            # bits and XOR (carry-less subtraction)
                dividend ⊻= divisor << i
            end
        end
        return dividend
    end

    function bit_length(n)
    #'''Compute the position of the most significant bit (1) of an integer.
    #   Equivalent to int.bit_length().'''

        bits = 0
        while n >> bits > 0
            bits += 1
        end
        return bits
    end

    ### Main GF multiplication routine ###

    result = cl_mult(x,y)
    # Then do a modular reduction (ie, remainder from the division) with an
# irreducible primitive polynomial so that it stays inside GF bounds
    if prim > 0
        result = cl_div(result, prim)
    end

    return result
end

function init_tables(prim=0x11d)
# '''Precompte the logarithm and anti-log tables for faster computation later, 
#    using the provided primitive polynomial.'''
    
    # 'prim' is the primitive (binary) polynomial. Since it's a polynomial in the 
    # binary sense, it's only in fact a single galois field value between 0 and 
    # 255, and not a list of gf values.
    global gf_exp = OffsetVector(zeros(UInt8,765), -255:509)
    global gf_log = zeros(Int16,255)
    # For each possible value in the galois field 2^8, we will pre-compute the 
    # logarithm and anti-logarithm (exponential) of this value.
    x = 0x0001
    for i=0:254
        global gf_exp[i] = x # Compute anti-log for this value and store it in a
                             # table.
        global gf_log[x] = i # Compute log at the same time.
        # x = gf_mult_noLUT(x, 2, prim)
        println("x_1=",x_1)
        # if you use only generator==2 or a power of 2, you can use the following 
        # which is fater than gf_mult_noLUT():

        x <<= 1    # multiply by 2 (change 1 by another number y to multiply by a 
                   # power of 2^y)
        if (x & 0x100) > 0    # similar to x >= 256, but a lot faster (because  
                              # 0x100 ==  256)
            x ⊻= prim    # subtract the primary polynomial to the current value 
                         # (instead of 255, so that we get a unique set made of 
                    # coprime numbers), this is the core of the tables generation.
        end
    end

    # Optimization: double the size of the anti-log table so that we don't need 
    # to mod 255 to stay inside the bounds (because we will mainly use this 
    # table for the multiplication of two GF number, no more).
    for i = 255:509
        global gf_exp[i] = gf_exp[i-255]
    end
    for i = -255:-1
        global gf_exp[i] = gf_exp[i+255]
    end
    
    return nothing
end

function gf_mult(x,y)
    if (x == 0) | (y == 0)
        return 0x0
    end
    return gf_exp[gf_log[x] + gf_log[y]]
end

function gf_div(x,y)
    if y == 0
        throw(DomainError(y, "Division by zero"))
    elseif x == 0
        return 0x0
    else
        return gf_exp[gf_log[x] - gf_log[y]]
    end
end

function gf_pow(x,power)
    return gf_exp[mod(power*gf_log[x], 0xff)]
end

function gf_inverse(x)
    return gf_exp[0xff - gf_log[x]]
end

function gf_poly_scale(p,x)
    return [gf_mult(p[i],x) for i in eachindex(p)]
end

function gf_poly_add(p,q)
    P = length(p)
    Q = length(q)
    R = maximum([P,Q])
    r = zeros(UInt8,R)
    # for i=1:P
    #     r[i+R-P] = p[i]
    # end
    r[(1+R-P):R] = p
    # for i=1:Q
    #     r[i+R-Q] ⊻= q[i]
    # end
    r[(1+R-Q):R] .⊻= q
    return r
end

function gf_poly_mult(p,q)
# '''Multiply two polynomials, inside Galois Field.'''

    # Pre-allocate the result array
    r = zeros(UInt8,length(p) + length(q) - 1)
    # compute the polynomial multiplicatio (just like the outer product of two
    # vectors, we multiply each coefficent of p with all coefficients of q)
    for j in eachindex(q)
        for i in eachindex(p)
            r[i+j-1] ⊻= gf_mult(p[i],q[j])
        end
    end
    return r
end

function gf_poly_eval(poly, x)
# '''Evaluates a polynomial in GF(2^p) given the value for x. This is based on 
#    Horner's scheme for maximum efficiency.'''

    y = poly[1]
    L = length(poly)
    for i in 2:L
        y = gf_mult(y,x) ⊻ poly[i]
    end
    return y
end

function rs_generator_poly(nsym)
# '''Generate an irreducible generator polynomial (necessary to encode a message
#    into Reed-Solomon).'''

    g = [1]
    for i=0:nsym-1
        g = gf_poly_mult(g, [1, gf_pow(2,i)])
    end
    return g
end

function gf_poly_div(dividend, divisor)
# '''Fast polynomial division by using Extended Synthetic Division and optimizes
#    for GF(2^p) computations (doesn't work with standard polynomials outside of
#    this galois field, see the wikipedia article for generic algorithm).'''

    # CAUTION: this function expects polynomials to follow the opposite convention
    # at decoding: the terms must go from the biggest to lowest degree (while most
    # other functions here expect a list from lowest to biggest degree).
    # e.g.: 1 + 2x + 5x^2 = [5, 2, 1], NOT [1, 2, 5]

    msg_out = copy(dividend) # Copy the dividend
    #normalizer = divisor[0]  # precomputing for performance
    for i = 1:(length(dividend) - length(divisor)+1)
        # msg_out[i] /= normalizer # for general polynomial division (when 
        # polynomials are non-monic), the usual way of using synthetic division
        # is to divide the divisor g(x) with its leading coefficients, but not
        # needed here.
        coef = msg_out[i] # precaching
        if coef != 0      # log(0) is undefined so we need to avoid that case 
                          # explicitly (and it's also a good optimization).
            for j = 2:length(divisor)
                # In synthetic division, we always skip the first coefficient of
                # the divisor, because it's only used to normalize the dividend
                # coefficient.
                if divisor[j] != 0 # log(0) is undefined
                    msg_out[i+j-1] ⊻= gf_mult(divisor[j], coef)
                    # equivalent to the more mathematically correct (but xoring 
                    # directly is faster): 
                    # msg_out[i+j-1] = -divisor[j] * coef
                end
            end
        end
    end
    # The resulting msg_out contains both the quotient and the remainder, the 
    # remainder being the size of the divisor (the remainder has necessarily the
    # same degree as the divisor -- not length but degree == length-1 -- since
    # it's what we couldn't divide from the dividend), so we computer the index
    # where this separation is, and return the quotient and remainder.
    separator = length(msg_out) - length(divisor) + 1
    return msg_out[1:separator], msg_out[separator+1:end] # return quotient and
                                                          # remainder
end

### ENCODING MAIN FUNCTION

function rs_encode_msg(msg_in, nsym)
# '''Reed-Solomon main encoding function'''

    gen = rs_generator_poly(nsym)

    # Pad the message, then divide it by the irreducible generator polyonomial
    _, remainder = gf_poly_div([msg_in; zeros(UInt8, length(gen)-1)], gen)
    # The remainder is our RS code! Just appent it to our original message to get
    # our full codeword (this represents a polynomial of max 256 terms).
    msg_out = [msg_in; remainder]

    return msg_out
end

function rs_encode_msg(msg_in, nsym)
# '''Reed-Solomon main encoding function, using polynomial division (algorithm
#    Extended Synthetic Division)'''

    L = length(msg_in)+nsym
    if L > 255
        throw(ArgumentError("Message is too long ("*string(L)*" when max is 255)"))
    end
    gen = rs_generator_poly(nsym)
    # Init msg_out with the values inside msg_in and pad with length(gen)-1 bytes
    # (which is the number of ecc symbols).
    msg_out = zeros(UInt8,L)
    # Initializing the Synthetic Division with the dividend (= input message 
    # polynomaial)
    msg_out[1:(L-nsym)] = msg_in

    # Synthetic division main loop
    for i in eachindex(msg_in)
        # Note that it's msg_out here, not msg_in. Thus, we reuse the updated
        # value at each iteration #(this is how Synthetic Division works: instead
        # of storing in a temporary register the intermediate values, we directly
        # commit them to the output)
        coef = msg_out[i]
        
        # log(0) is undefiend, so we need to manually check for this case. There
        # is no need to check the divisor here because we know it can't be 0 since
        # we generated it.
        if coef != 0
            # in synthetic division, we always skip the first coefficient of the
            # divisor, because it's only used to normalize the dividend coefficient
            # (which is here useless since the divisor, the generated polynomial,
            # is always monic.)
        G = length(gen)
            for j = 2:G
                msg_out[i+j-1] ⊻= gf_mult(gen[j], coef)
            end
        end
    end
    
    # At this point, the Extended Synthetic Division is done, msg_out contains 
    # the quotient in msg_out[1:length(msg_in)] (which represents the RS code), 
    # so we can just overwrite the quotient with the input message, so that we
    # get our complete codeword composed of the message+code.
    msg_out[1:(L-nsym)] = msg_in

    return msg_out

end

function rs_calc_syndromes(msg, nsym)
# '''Given the received codeword msg and the number of error correcting symbols
#    (nsym), computes the syndromes polynomial. Mathematically, it's essentially
#    equivalent to a Fourier Transform (Chein search being the inverse).'''

    # Note the "[0; synd]": we add a 0 coefficient for the lowest degree (the 
    # constant). This effectively shifts the syndrome, and will shift every
    # computations depending on the syndromes (such as the errors locator
    # polynomial, errors evaluator polynomial etc., but not the errors positions).
    # This is not necessary: you can adapt subsequent computations to start from
    # 0 instead of skipping the first iteration (i.e., the often seen 
    # range(2,n-k+1) in python).

    synd = zeros(UInt8, nsym)
    for i in eachindex(synd)
        synd[i] = gf_poly_eval(msg, gf_pow(2,i-1))
    end
    return [0; synd]
end

function rs_check(msg, nsym)
# '''Returns true if the message + ecc has no error or false otherwise (may not 
#    always catch a wrong decoding or a wrong message, particularly if there are
#    too many errors -- above the Singleton bound --, but it usually does)'''

    return ( maximum(rs_calc_syndromes(msg, nsym)) == 0 )
end

function rs_find_errata_locator(e_pos)
# '''Compute the erasures/errors/errata locator polynomial from the erasures/errors
#    /errata positions (the positions must be relative to the x coefficient, eg:
#    "hello worldxxxxxxxxx" is tampered to "h_ll_ worldxxxxxxxxx" with xxxxxxxxx
#    being the ecc of length n-k=9, here the string positions are [1, 4], but the
#    coefficients are reversed since the ecc characters are placed as the first 
#    coefficients of the polynomial, thus the coefficients of the erased characters
#    are n-1 - [1, 4] = [18, 15] = erasures_loc to be specified as an argument.'''

    e_loc = [1] # just to init because we will multiply, so it must be 1 so that
                # the multiplication starts correctly without nulling any term 
    # erasures_loc = product(1 - x*alpha^i) for i in erasures_pos and where alpha
    # is the alpha chosen to evaluate polynomials.
    for i in e_pos
        e_loc = gf_poly_mult(e_loc, gf_poly_add([1], [gf_pow(2, i), 0]))
    end
    return e_loc
end

function rs_find_error_evaluator(synd, err_loc, nsym)
#'''Compute the error (or erasures if you supply sigma=erasures locator
#   polynomial, or errata) evaluator polynomial Omega form the syndrome and
#   the error/erasures/errata locator Sigma.'''

    # Omega(x) = [ Synd(x) * Error_loc(x) ] mod x^(n-k+1)
    #-, remainder = gf_poly_div(gf_poly_mult(synd, err_loc), [1; zeros(UInt8, nsym+1)])
        # fist multiply syndromes * errata_locator, then do a polynomial division to
        # truncate the polynomial to the required length.
    # Faster way that is equivalent:
    remainder = gf_poly_mult(synd,err_loc) # first multiply the syndromes with the
                                          # errata locator polynomial
    remainder = remainder[length(remainder) - nsym:end] # then slice the list to
                                                        # truncate it (which
                                                        # represents the polynomial),
                                                        # which is equivalent to
                                                        # dividing by a polynomial
                                                        # of the length we want

    return remainder
end

function rs_correct_errata(msg_in, synd, err_pos)
#'''Forney algorithm, computes the values (error magnitudes) to correct the input
#   message.'''

    # calculate errata locator polynomial to correct both errors and erasures (by
    # combining the errors positions given by the error locator polynomial found
    # by BM with the erasures positions given by caller)
    coef_pos = [length(msg_in) - p for p in err_pos] # need to convert the 
                                                         # positions to coefficients
                                                         # degrees for the errata
                                                         # locator also to work 
                                                         # (e.g.: instead of [0, 1, 2]
                                                         # it will become [lenght(msg)-1,
                                                         # lenght(msg)-2, legth(msg)-3])
    err_loc = rs_find_errata_locator(coef_pos)
    # calculate errata evaluator polynomial (often called Omega or Gamma in academic
    # papers)
    err_eval = rs_find_error_evaluator(synd[end:-1:1], err_loc, length(err_loc)-1)
    err_eval = err_eval[end:-1:1]

    # Second part of Chien search to get the error location polynomial X from the
    # error positions in err_pos (the roots of the error locator polynomial, i.e.,
    # where it evaluates to 0)
    X = []  # will store the position of the errors
    for i in eachindex(coef_pos)
        ell = 255 - coef_pos[i]
        append!(X,gf_pow(2,-ell))
    end

    # Forney algorithm: compute the magnitudes
    E = zeros(UInt8, length(msg_in))    # will store the values that need to be 
                                        # corrected (substracted) to the message
                                        # containing errors. This is sometimes
                                        # called the error magnitude polynomial.
    for (i, Xi) in enumerate(X)

        Xi_inv = gf_inverse(Xi)

        # Compute the formal derivative of the error locator polynomial (see Blahut,
        # Algebraic codes for data transmition, pp. 196-197).
        # the formal derivative of the errata locator is used as the denominator
        # of the Forney Algorithm, which simply says that the ith error value is
        # given by error_evaluator(gf_inverse(Xi))/error_locator_derivative(gf_inverse(Xi)).
        # See Blahut, ibid.
        err_loc_prime_tmp = []
        for j in eachindex(X)
            if j != i
                append!(err_loc_prime_tmp, 1 ⊻ gf_mult(Xi_inv, X[j]))
            end
        end
        # compute the product, which is the denominator of the Forney algorithm
        # (errata locator derivative )
        err_loc_prime = 1
        for coef in err_loc_prime_tmp
            err_loc_prime = gf_mult(err_loc_prime, coef)
        end
        # equivalent to: err_loc_prime = functools. reduce(gf_mult, err_loc_prime_temp, 1)

        # Compute y (evaluation of the errata evaluator polynomial)
        # This is a more faithful translation of the theoretical equation contrary
        # to the old forney method. Here it is an exact reproduction:
        # yl = omega(xl.inverse())/prod(1 - Xj*Xl.inverse()) for j in length(X)
        y = gf_poly_eval(err_eval[end:-1:1], Xi_inv) # numerator of the Forney 
                                                     # algorithm (errata evaluator
                                                     # evaluated)
        y = gf_mult(gf_pow(Xi, 1), y)

        # Check: err_loc_prime (the divisor) should not be zero.
        if err_loc_prime == 0
            throw(ReedSolomonError("Could not find error magnitude"))
        end

        # Compute the magnitude
        magnitude = gf_div(y, err_loc_prime) # magnitude value of the error,
                                             # calculated by the Forney algorithm
                                             # (an equation in fact): dividing the
                                             # errata evaluator with the errata
                                             # locator derivative gives us the
                                             # errata magnitude (ie. value to repair)
                                             # the ith symbol.
        E[err_pos[i]] = magnitude # store the magnitude for this error into the
                                  # magnitude polynomial
        
        # Apply the correction of values to get our message corrected! (note that
        # the ecc bytes also gets corrected!)
        # (this isn't the Forney algorithm, we just apply the result of decoding
        # here)
    end
    msg_in = gf_poly_add(msg_in, E) # equivalent to Ci = Ri - Ei where Ci is the
                                    # correct message, Ri the received (senseword)
                                    # message, and Ei the errata # magnitudes 
                                    # (minus is replaced by XOR) since it's 
                                    # equivalent in GF(2^p)). So in fact here we
                                    # subtract from the received message the errors
                                    # magnitude, which logically corrects the value
                                    # to what it should be.
 
    return msg_in
end

function rs_find_error_locator(synd, nsym; erase_loc=nothing, erase_count=0)
#'''Find error/errata locator and evaluator polynomials with Berlekamp-Massey
#   algorithm.'''
    # The idea is that BM will iteratively estimate the error locator polynomial.
    # To do this, it will compute a Discrepancy term called Delta, which will
    # tell us if the error locator polynomial needs an update or not (hence why
    # it's called Discrepancy: it tells us when we are getting off board from the
    # correct value).

    # Init the polynomials
    if erase_loc !== nothing # if the erasure locator polynomial is supplied, we
                             # init with its value, so that we include erasures
                             # in the final locator polinomial
        err_loc = copy(erase_loc)
        old_loc = copy(erase_loc)
    else
        err_loc = [1] # This is the main variable we want to fill, also called
                      # Sigma in other notations or more formally the errors/errata
                      # locator polynomial.
        old_loc = [1] # BM is an iterative algorithm, and we need the errata locator
                      # polynomial of the previous iteration in order to updated
                      # other necessary variables.
    end
    #L = 0 # update flag variable, not needed here because we use an alternative
    #      # equivalent way of checking if update is needed (but using the flag
    #      # could potentially be faster depending on if using length(list) is 
    #      # taking linear time in your language.)

    # Fix the syndrome shifting: when computing the syndrome, some implementations
    # may prepend a 0 coefficient for the lowest degree term (the constant). This
    # is a case of syndrome shifting, thus the syndrome will be bigger than the 
    # number of ecc symbols (I don't know what purpose serves this shifting). If
    # that's the case, then we need to account for the syndrome shifting when we
    # use the syndrome such as inside BM, by skipping those prepended coefficients.
    # Another way to detect the shifting is to detect the 0 coefficients: by
    # definition, a syndrome does not contain any 0 coefficient (except if there
    # are no errors/erasures, in this case they are all 0). This however doesn't
    # work with the modified Forney syndrome, which set to 0 the coefficients
    # corresponding to erasures, leaving only the coefficients correponding to
    # errors.
    synd_shift = length(synd) - nsym

    for i = 0:(nsym-erase_count-1) # generally: nsym-erase_count == length(synd),
                                 # except when you input a partial erase_loc and
                                 # using the full syndrome instead of the Forney
                                 # syndrome, in which case nsym-erase_count is 
                                 # more correct(length(synd) will fail badly with
                                 # IndexError).
        if erase_loc !== nothing # if an erasures locator polynomial was provided
                                 # to init the errors locator polynomial, then 
                                 # we must skip the FIRST erase_count iterations
                                 # (not the last iterations, this is very important!)
            K = erase_count + i + synd_shift
        else # if erasures locator is not provided, then either there's no erasures
             # to account or we use the Forney syndromes, so we don't need to use
             # erase_count nor erase_loc (the erasures have been trimmed our of 
             # the Forney syndromes).
            K = i + synd_shift
        end

        # Compute the discrepancy Delta
        # Here is the close-to-the-books operation to compute the discrepancy Delta:
        # it's a simple polynomial multiplication of error locator with the syndromes,
        # and then we get the kth element.
        #delta = gf_poly_mult(err_loc[end:-1:1], synd)[K] # theoretically it should
                                    # be gf_poly_add(synd[end:-1:1], [1])[end:-1:1]
                                    # instead of just synd but it seems it's not 
                                    # absolutely necessary to correctly decode.
        # But this can be optimized: since we only need the kth element, we don't
        # need to compute the polynomial multiplication for any other element but
        # the kth. Thus, to optimize, we compute the poly_mult only at the item
        # we need, skipping the rest (avoiding a nested loop, thus we are linear
        # time instead of quadratic).
        # This optimization is actually described in several figures of the book
        # [Blahut, 2003].
        delta = synd[K+1]
        for j=1:length(err_loc)-1
            index = (K+1)-j
            if index < 1
                index = index + length(synd)
            end
            delta ⊻= gf_mult(err_loc[end - j], synd[index]) # delta is also called
                                    # discrepancy. Here we do a partial polynomial
                                    # multiplication (i.e., we compute the 
                                    # polynomial multiplication only for the term
                                    # of degree K). Should be equivalent to
                                    # brownanrs.polynomials.mul_at().
        end
        # println("delta: ", delta)
        # println("confirm: ", gf_poly_mult(err_loc[end:-1:1], synd)[K+1])            
        
        # Shift polynomials to compute the next degree
        append!(old_loc, 0)

        # Iteratively estimate the errata locator and evaluator polynomials
        if delta != 0 # Update only if there's a discrepancy
            if length(old_loc) > length(err_loc) # Rule B (Rule A is implicitly 
                                    # defined because rule A just says that we skip
                                    # any modification for this iteration
            #if 2*L <= K+erase_count # equivalent to length(old_loc) > length(err_loc),
            #                        # as long as L is correctly computed.
                # Computing errata locator polynomial Sigma
                new_loc = gf_poly_scale(old_loc, delta)
                old_loc = gf_poly_scale(err_loc, gf_inverse(delta)) # effectively
                                    # we are doing err_loc * 1/delta = err_loc // delta
                err_loc = copy(new_loc)
                # Update the update flag
                #L = K -L # the update flag L is tricky: in blahut's schema, it'same
                # mandatory to use 'L = K - L - erasue_count' (and indeed in a 
                # previous draft of this function, if you forgot to do '-erase_cout'
                # it would lead to correcting only 2*(errors+erasures) <= (n-k)
                # instead of 2*errors+ erasures <= (n-k)), but in this latest draft,
                # this will lead to a wrong decoding in some cases where it should
                # correctly decode! Thus you should try with and without '-erase_count'
                # to update L on your own implementation and see which one works
                # OK without producing wrong decoding failures.
            end

            # Update with the discrepancy
            err_loc = gf_poly_add(err_loc, gf_poly_scale(old_loc, delta))
        end
    end

    # Check if the result is correct, that there's not too many errors to correct
    while (length(err_loc) > 0) && (err_loc[1] == 0)
        err_loc = err_loc[2:end]
    end
    errs = length(err_loc) - 1
    if (errs-erase_count)*2 + erase_count > nsym
        throw(ReedSolomonError("Too many errors to correct"))
    end

    return err_loc

end

function rs_find_errors(err_loc, nmess) # nmess is length(msg_in)
#'''Find the roots (i.e., where evaluation = zero) of error polynomial by brute-
#   force trial, this is a sort of Chien's search (but less efficient, Chein's
#   search is a way to evaluate the polynomial such that each evaluation only takes
#   constant time).'''

    errs = length(err_loc) - 1
    err_pos = []
    for i=0:nmess-1 # normally we should try all 2^8 possible values, but
                            # here we optimize to just check the interesting symbols
        if gf_poly_eval(err_loc, gf_pow(2,i)) == 0; # it's a 0? Bingo, it's a root
                            # of the error locator polynomial, in other terms is
                            # the location of an error.
            append!(err_pos, nmess - i)
        end
    end
    # Sanity check: the number of errors/errata positions found should be exactly
    # the same as the length of the errata locator polynomial
    if length(err_pos) != errs # couldn't find error locations
        # throw(ReedSolomonError("Too many (or few) errors found by Chien Search for the errata locator polynomial!"))
        throw(ReedSolomonError("Too many (or few) errors found by Chien Search for the errata locator polynomial!"))
    end

    return err_pos[end:-1:1]
end

function rs_forney_syndromes(synd, pos, nmess)
#'''Compute Forney syndromes, which computes modified syndromes to compute only 
#   errors (erasures are trimmed out). Do not confuse this with Forney algorithm,
#   which allows to correct the message bases on the location of errors.

    erase_pos_reversed = [nmess-p for p in pos] # prepare the coefficient degree
                                                  # positions (instead of the erasures
                                                  # positions).

    # Optimized method, all operations are inlined
    fsynd = copy(synd[2:end])
    for i in eachindex(pos)
        x = gf_pow(2, erase_pos_reversed[i])
        for j = 1:length(fsynd)-1
            fsynd[j] = gf_mult(fsynd[j], x) ⊻ fsynd[j+1]
        end
    end

    # Equivalent, theoreical way of computing the modified Forney syndromes:
    # fsynd = (erase_loc * synd) % x^(n-k)
    # See Shao, H. M., Truong, T. K., Deutsch, L. J., $ Reed, I. S. (1086, April).
    # A single chip VLSI Reed-Solomon decoder. In Acoustics, Speech and Signal
    # Processing, IEEE International Conference pm ICASSP'86 (Vol. II, pp. 2151-5154).
    #erase_loc = rs_find_errata_locator(erase_pos_reversed, generator=generator)
        #computing the erasures locator polynomial
    #fsynd = gf_poly_mul(erase_loc[end:-1:1], synd[2:end]) 
        # then multiply with the syndrome to get the untrimed forney syndrome
    #fsynd = fsynd[length(pos)+1:end] # then trim the first erase_pos coefficients
                                      # which are useless. Seems to be not necessary,
                                      # but this reduces the computation time later
                                      # in BM (thus it's an optimization).

    return fsynd
end

function rs_correct_msg(msg_in, nsym, erase_pos=nothing)
#'''Reed-Solomon main decoding function'''

    if length(msg_in) > 255 # can't decode, message is too bigger
        throw(ArgumentError("Message is too long ("*string(L)*" when max is 255)"))
    end

    msg_out = copy(msg_in)  # copy the message
    # erasures: set them to null bytes for easier decoding (but this is not necessary,
    # they will be corrected anyway, but debbuging will be easier with null bytes
    # because the error locator polynomial values will only depend on the errors
    # locations, not their values).
    if erase_pos === nothing
        erase_pos = []
    else
        for e_pos in erase_pos
            msg_out[e_pos] = 0x00
        end
    end
    # check if there are too many erasures to correct (beyond the Singleton
    # bound)
    if length(erase_pos) > nsym
        throw(ReedSolomonError("Too many erasures to correct"))
    end
    # prepare the syndrome polynomial using only errors (i.e. errors = characters
    # that were either replaced by null bytes or changed to another character,
    # but we don't know their positions)
    synd = rs_calc_syndromes(msg_out, nsym)
    # check if there's any error/erasure in the input codeword. if not (all 
    # syndromes coefficients are 0), then just return the message as-is.
    if maximum(synd) == 0
        return msg_out[1:end-2], msg_out[end-1:end] # no errors
    end

    # compute the Forney syndromes, which hide the erasures from the original
    # syndrome (so that BM will just have to deal with errors, not erasures)
    fsynd = rs_forney_syndromes(synd, erase_pos, length(msg_out))
    # compute the error locator polynomial sing Berlekamp-Massey
    err_loc = rs_find_error_locator(fsynd, nsym, erase_count=length(erase_pos))
    println("err_loc=",1 .*err_loc)
    # locate the message errors using Chien search (or brute-force search)
    err_pos = rs_find_errors(err_loc[end:-1:1], length(msg_out))
    if err_pos === nothing
        throw(ReedSolomonError("Could not locate error"))
    end
            
    # Find errors values and apply them to correct the message
    # compute errata evaluator and errata magnitude polynomials, then correct errors
    # and erasures.
    msg_out = rs_correct_errata(msg_out, synd, [erase_pos; err_pos]) # note that
        # we here use the original syndrome, not the forney syndrome.
    
# (because we will correct both errors and erasures, so we need the full syndrome)

    # check if the final message is fully repaired
    synd = rs_calc_syndromes(msg_out, nsym)
    if maximum(synd) > 0
        throw(ReedSolomonError("Could not correct message"))
    end
    # return the sucessfully decoded message
    return msg_out[1:end-nsym], msg_out[end-nsym+1:end] # also return the corrected
        # ecc block so that the user can check()
end

# Configuration of the parameters and input message
# prim = 0x11d
n = 20 # set the size you want, it must be > k, the remaining n-k symbols will be the ECC code (more is better)
k = 10 # k = len(message)
# message = "hello world" # input message
message = collect(1:k)


# Initializing the log/antilog tables
init_tables()

# Encoding the input message
# mesecc = rs_encode_msg([Int(x) for x in message], n-k)
mesecc = rs_encode_msg(message, n-k)
println("Original:", "\n", 1*mesecc)

# Tampering 6 characters of the message (over 9 ecc symbols, so we are above the Singleton Bound)
mesecc[1] = 0
mesecc[2] = 0
mesecc[3] = 0
mesecc[4] = 0
# mesecc[5] = 0
# mesecc[6] = 0
# mesecc[7] = 0
println("Corrupted:","\n", 1*mesecc)

# Decoding/repairing the corrupted message, by providing the locations of a few erasures, we get below the Singleton Bound
# Remember that the Singleton Bound is: 2*e+v <= (n-k)
erase_pos=[4,5]
corrected_message, corrected_ecc = rs_correct_msg(mesecc, n-k, erase_pos)
print("Repaired: ", "\n", 1 .*[corrected_message; corrected_ecc])
# Created on June, 2022
# author: AllanEduardo42
# This code is an adaptation of that foun