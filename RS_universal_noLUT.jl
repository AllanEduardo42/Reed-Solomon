# Created on September, 2022
# author: AllanEduardo42
# This code is an adaptation of that found in:
# https://en.wikiversity.org/wiki/Reed%E2%80%93Solomon_codes_for_coders

# ==============================================================================
#                       Reed Solomon coding and decoding
# =============================================================================

struct ReedSolomonError <: Exception
    msg::AbstractString
end

PRIM = 47
GEN = 47
C_EXP = 2
PRIM_POLY = zeros(Int,C_EXP+1)
PRIM_POLY[1] = 1
PRIM_POLY[2] = 45
PRIM_POLY[3] = 5

function mod_add(x,y)
    if x >= gf_prim
        throw(ArgumentError("x must be a number such that 0 "*string(≤)*" x < "*string(gf_prim)*"."))
    end
    if y >= gf_prim
        throw(ArgumentError("y must be a number such that 0 "*string(≤)*" y < "*string(gf_prim)*"."))
    end
    return rem(x+y,gf_prim)
end

function mod_sub(x,y)
    if x >= gf_prim
        throw(ArgumentError("x must be a number such that 0 "*string(≤)*" x < "*string(gf_prim)*"."))
    end
    if y >= gf_prim
        throw(ArgumentError("y must be a number such that 0 "*string(≤)*" y < "*string(gf_prim)*"."))
    end
    return mod_add(x, mod_oposite[y+1])
end

function mod_mult(x,y)
    if x >= gf_prim
        throw(ArgumentError("x must be a number such that 0 "*string(≤)*" x < "*string(gf_prim)*"."))
    end
    if y >= gf_prim
        throw(ArgumentError("y must be a number such that 0 "*string(≤)*" y < "*string(gf_prim)*"."))
    end
    return rem(x*y,gf_prim)
end

function mod_div(x,y)
    if x >= gf_prim
        throw(ArgumentError("x must be a number such that 0 "*string(≤)*" x < "*string(gf_prim)*"."))
    end
    if y >= gf_prim
        throw(ArgumentError("y must be a number such that 0 "*string(≤)*" y < "*string(gf_prim)*"."))
    end
    return mod_mult(x,mod_inverse[y])
end

function gf_mult_noLUT(p, q)

    if q == gf_generator # just shift the polynomial
        result = [p; 0]
    elseif p == gf_generator
        result = [q; 0]
    else
        # '''Multiply two polynomials, inside Galois Field.'''            
        # Pre-allocate the result array
        result = zeros(Int, length(p) + length(q) - 1)
        # compute the polynomial multiplication (just like the outer product of two
        # vectors, we multiply each coefficent of p with all coefficients of q)
        for j in eachindex(q)
            if q[j] != 0
                for i in eachindex(p)
                    if p[i] != 0
                        result[i+j-1] =  mod_add(result[i+j-1], mod_mult(p[i], q[j]))
                    end
                end
            end
        end    
    end
    if length(result) >= length(gf_prim_poly)
        ___, result = gf_div_noLUT(result, gf_prim_poly)
    end
    i = 1
    while (result[i] == 0) && (i < length(result))
        i+=1
    end
    return result[i:end]
end

function gf_div_noLUT(dividend, divisor)

    # convert the prime polinomial

    # remove leading zeros
    while divisor[1] == 0
        divisor = divisor[2:end]
    end
    normalizer = divisor[1]
    L1 = length(dividend)
    L2 = length(divisor)
    for i = 1:(L1-L2+1)
        dividend[i] = mod_div(dividend[i], normalizer) # for general polynomial division (when polynomials are non-monic), the usual way of using synthetic division is to divide the divisor g(x) with its leading coefficient.
        coef = dividend[i] # precaching
        if coef != 0 # log(0) is undefined, so we need to avoid that case explicitly (and it's also a good optimization).
            for j=2:L2 # in synthetic division, we always skip the first coefficient of the divisior,
                                              # because it's only used to normalize the dividend coefficient
                if divisor[j] != 0 # log(0) is undefined
                    dividend[i+j-1] = mod_sub(dividend[i+j-1], mod_mult(divisor[j], coef)) # equivalent to the more mathematically correct
                                                               # (but xoring directly is faster): dividend[i + j] += -divisor[j] * coef
                end
            end
        end
    end

    # The resulting dividend contains both the quotient and the remainder, the remainder being the size of the divisor
    # (the remainder has necessarily the same degree as the divisor -- not length but degree == length-1 -- since it's
    # what we couldn't divide from the dividend), so we compute the index where this separation is, and return the quotient and remainder.
    separator = length(dividend) - length(divisor) + 1
    return dividend[1:separator], dividend[separator+1:end]

end

function init_oposites()
    
    global mod_oposite = zeros(Int, gf_prim+1)
    for i=1:gf_prim
        mod_oposite[i+1] = rem(gf_prim-i, gf_prim)
    end

end

function init_inverses()

    global mod_inverse = zeros(Int, gf_prim-1)
    for i=1:gf_prim-1
        for j=0:gf_prim-1
            N = gf_prim*j + 1
            if rem(N, i) == 0
                mod_inverse[i] = N ÷ i
                break
            end
        end
    end

    return nothing
end

function init_tables()

    global gf_exp = [] # anti-log (exponential) table
    global gf_log = zeros(Int, field_charac) # log table, log[0] is impossible and thus unused
    x = [0, 1]
    for i=1:field_charac
        x = gf_mult_noLUT(x, gf_generator)
        append!(gf_exp, anti_gf_convert(x)) # compute anti-log for this value and store it in a table
        gf_log[anti_gf_convert(x)] = i # compute log at the same time
    end
    # Optimization: double the size of the anti-log table so that we don't need to mod 255 to stay inside the bounds (because we will mainly use this table for the multiplication of two GF numbers, no more).

    # for i=(field_charac+1):(field_charac * 2)
    #     gf_exp[i] = gf_exp[i - field_charac]
    # end
    # return [gf_log, gf_exp]
end

function gf_convert(x)

    if length(x) > 1
        return x
    end
    quocient = x ÷ convert_generator
    remainer = rem(x, convert_generator)
    coeffs = [remainer]
    i = 1
    while quocient >= convert_generator
        remainer = rem(quocient, convert_generator)
        quocient = quocient ÷ convert_generator
        prepend!(coeffs,remainer)
        i += 1
    end
    if quocient != 0
        prepend!(coeffs, quocient)
    end

    return coeffs

end

function anti_gf_convert(x)
    r = Int128(0)
    for i=0:length(x)-1
        r += x[end-i]*(convert_generator^i)
    end
    return r
end

function gf_add(p, q)
    P = length(p)
    Q = length(q)
    R = maximum([P,Q])
    r = zeros(Int,R)
    for i=1:P
        r[i+R-P] = p[i]
    end
    for i=1:Q
        r[i+R-Q] = mod_add(r[i+R-Q], q[i])
    end
    i=1
    while (r[i] == 0) && (i < R)
        i+=1
    end
    return r[i:end]
end

function gf_oposite(p)
    return  [mod_oposite[p[i]+1] for i in eachindex(p)]
end
    
function gf_sub(x, y)
    return gf_add(x, gf_oposite(y))
end

function gf_mult(x,y)
    if (x == [0]) | (y == [0])
        return [0]
    end
    return gf_mult_noLUT(x, y)
end

function gf_div(x,y)
    if y == [0]
        throw(DomainError(y, "Division by zero"))
    end
    if x == [0]
        return 0x0
    end
    return gf_div_noLUT(x,y)
end

function gf_pow(x,power)
    if power == 0
        return 1
    end
    if x == [1]
        return [1]
    end
    # if (power > 10000) || power < 0
    if power == 1
        if x != gf_generator
            expon = Int128(0)
            y = [1]
            while y != x
                y = gf_mult(y, gf_generator)
                expon += 1
                if expon > field_charac
                    break
                end
            end
        else
            expon = Int128(1)
            y = x
        end
        if power > 0
            idx = expon*power
            if idx < field_charac      
                for i=1:(power-1)
                    y = gf_mult(y, x)
                end
            else
                y = [1]
                for i=1:rem(idx, field_charac)
                    y = gf_mult(y,gf_generator)
                end
            end            
        else
            idx = expon*(field_charac + power) 
            if idx < field_charac
                for i=1:idx-expon
                    y = gf_mult(y, gf_generator)
                end
            else
                y=[1]
                for i=1:rem(idx, field_charac)
                    y = gf_mult(y,gf_generator)
                end
            end
        end
    else
        y = x
        for i=2:power
            y = gf_mult(y,x)
        end
    end
    return y
end

function gf_inverse(x)
    if x == [0]
        throw(DomainError(y, "Division by zero"))
    else
        return gf_pow(x,-1)
    end
end

function gf_poly_scale(p,x)
    return [gf_mult(p[i],x) for i in eachindex(p)]
end

function gf_poly_add(p, q)
    P = length(p)
    Q = length(q)
    R = maximum([P,Q])
    r = zeros(Int,R)
    for i=1:P
        r[i+R-P] = p[i]
    end
    for i=1:Q
        r[i+R-Q] = gf_add(r[i+R-Q], q[i])
    end
    return r
end

function gf_poly_oposite(p)
    return [gf_oposite(p[i]) for i in eachindex(p)]
end

function gf_poly_sub(p,q)
    P = length(p)
    Q = length(q)
    R = maximum([P,Q])
    r = [[0] for i=1:R]
    for i=1:P
        r[i+R-P] = p[i]
    end
    for i=1:Q
        r[i+R-Q] = gf_sub(r[i+R-Q], q[i])
    end
    return r
end

function gf_poly_mult(p,q)
# '''Multiply two polynomials, inside Galois Field.'''
    # Pre-allocate the result array
    r = [[0] for i=1:(length(p) + length(q) - 1)]
    # compute the polynomial multiplication (just like the outer product of two
    # vectors, we multiply each coefficent of p with all coefficients of q)
    for j in eachindex(q)
        for i in eachindex(p)
            r[i+j-1] =  gf_add(r[i+j-1], gf_mult(p[i],q[j]))
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
        y = gf_add(gf_mult(y,x), poly[i])
    end
    return y
end

function rs_generator_poly(nsym)
# '''Generate an irreducible generator polynomial (necessary to encode a message
#    into Reed-Solomon).'''

    g = [[1]]
    for i=0:nsym-1
        g = gf_poly_mult(g, [[[1]]; gf_poly_oposite([gf_pow(gf_generator,i)])])
    end
    # Note that we remove the leading "1" coefficient, since the generator poli
    # nomial is always monic.
    return g[2:end]
end

# function rs_generator_poly(nsym, generator)
#     # '''Generate an irreducible generator polynomial (necessary to encode a message
#     #    into Reed-Solomon).'''
    
#         g = [1]
#         for i=0:nsym-1
#             g = gf_poly_mult(g, [1; gf_poly_oposite(gf_pow(generator,i))])
#             println()
#         end
#         # Note that we remove the leading "1" coefficient, since the generator poli
#         # nomial is always monic.
#         return g[2:end]
#     end

function gf_poly_div(dividend, divisor)

    msg_out = copy(dividend) # Copy the dividend
    normalizer = divisor[1] # precomputing for performance
    L1 = length(msg_out)
    L2 = length(divisor)
    if L1 < L2
        return msg_out
    end
    for i = 1:L1-L2+1
        msg_out[i] = gf_div(msg_out[i], normalizer) # for general polynomial division (when polynomials are non-monic), the usual way of using
                                  # synthetic division is to divide the divisor g(x) with its leading coefficient, but not needed here.
        coef = msg_out[i] # precaching
        if coef != 0 # log(0) is undefined, so we need to avoid that case explicitly (and it's also a good optimization).
            for j=2:L2 # in synthetic division, we always skip the first coefficient of the divisior,
                                              # because it's only used to normalize the dividend coefficient
                if divisor[j] != 0 # log(0) is undefined
                    msg_out[i+j-1] = gf_sub(msg_out[i+j-1], gf_mult(divisor[j], coef)) # equivalent to the more mathematically correct
                                                               # (but xoring directly is faster): msg_out[i + j] += -divisor[j] * coef
                end
            end
        end
    end

    # The resulting msg_out contains both the quotient and the remainder, the remainder being the size of the divisor
    # (the remainder has necessarily the same degree as the divisor -- not length but degree == length-1 -- since it's
    # what we couldn't divide from the dividend), so we compute the index where this separation is, and return the quotient and remainder.
    separator = length(msg_out) - length(divisor) + 1
    return msg_out[1:separator], msg_out[separator+1:end] # return quotient, remainder.

end

# function rs_encode_msg(msg_in, nsym)
#     # '''Reed-Solomon main encoding function'''
    
#         pgen = [1; rs_generator_poly(nsym)]
    
#         # Pad the message, then divide it by the irreducible generator polyonomial
#         _, remainder = gf_poly_div([msg_in; zeros(Int, length(pgen)-1)], pgen)
#         # The remainder is our RS code! Just appent it to our original message to get
#         # our full codeword (this represents a polynomial of max 256 terms).
#         msg_out = [msg_in; gf_poly_sub([0], remainder)]
    
#         return msg_out
# end

function rs_encode_msg(msg_in, nsym; generator=GEN, prim=PRIM, prim_poly=PRIM_POLY, c_exp=C_EXP)
    # '''Reed-Solomon main encoding function, using polynomial division (algorithm
    #    Extended Synthetic Division)'''
    global gf_prim = prim
    global gf_exp = c_exp
    global field_charac = Int128(prim)^c_exp - 1    
    init_oposites()
    init_inverses()
    
    global convert_generator = Int128(generator)
    global gf_prim_poly = gf_convert(prim_poly)    
    global gf_generator = [1, 0]

    L = length(msg_in)+nsym
    if L > field_charac
        throw(ArgumentError("Message is too long ("*string(L)*" when max is "*string(field_charac)*" )"))
    end
    gen = rs_generator_poly(nsym)
    # Init msg_out with the values inside msg_in and pad with length(gen)-1 bytes
    # (which is the number of ecc symbols).
    msg_out = [[0] for i=1:L]
    # Initializing the Synthetic Division with the dividend (= input message 
    # polynomaial)
    msg_out[1:(L-nsym)] = [gf_convert(msg_in[i]) for i=1:L-nsym]

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
            for j in eachindex(gen)
                msg_out[i+j] = gf_sub(msg_out[i+j], gf_mult(gen[j], coef))
            end
        end
    end
    
    # At this point, the Extended Synthetic Division is done, msg_out contains 
    # the quotient in msg_out[1:length(msg_in)] (which represents the RS code), 
    # so we can just overwrite the quotient with the input message, so that we
    # get our complete codeword composed of the message+code.
    separator = length(msg_in)
    msg_out[1:separator] = [gf_convert(msg_in[i]) for i=1:L-nsym]
    msg_out[separator+1:end] = gf_poly_oposite(msg_out[separator+1:end])

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

    # synd = [[0] for i=1:nsym]
    synd = []
    for i=1:nsym
        append!(synd,[gf_poly_eval(msg, gf_pow(gf_generator,i-1))])
    end
    return [[[0]]; synd]
end

function rs_forney_syndromes(synd, pos, nmess, generator)
    #'''Compute Forney syndromes, which computes modified syndromes to compute only 
    #   errors (erasures are trimmed out). Do not confuse this with Forney algorithm,
    #   which allows to correct the message bases on the location of errors.
    
        erase_pos_reversed = [nmess-p for p in pos] # prepare the coefficient degree
                                                      # positions (instead of the erasures
                                                      # positions).
    
        # Optimized method, all operations are inlined
        # fsynd = copy(synd[2:end])
        # for i in eachindex(pos)
        #     x = gf_pow(generator, erase_pos_reversed[i])
        #     for j = 1:length(fsynd)-1
        #         fsynd[j] = gf_add(gf_mult(fsynd[j], x), fsynd[j+1])
        #     end
        # end
        # Equivalent, theoretical way of computing the modified Forney syndromes:
        # fsynd = (erase_loc * synd) % x^(n-k)
        # See Shao, H. M., Truong, T. K., Deutsch, L. J., $ Reed, I. S. (1086, April).
        # A single chip VLSI Reed-Solomon decoder. In Acoustics, Speech and Signal
        # Processing, IEEE International Conference pm ICASSP'86 (Vol. II, pp. 2151-5154).
        erase_loc = rs_find_errata_locator(erase_pos_reversed)
            # computing the erasures locator polynomial
        fsynd = gf_poly_mult(erase_loc[end:-1:1], synd[2:end]) 
            # then multiply with the syndrome to get the untrimed forney syndrome
        fsynd = fsynd[length(pos)+1:end] # then trim the first erase_pos coefficients
                                         # which are useless. Seems to be not necessary,
                                         # but this reduces the computation time later
                                         # in BM (thus it's an optimization).
    
        return fsynd
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
        err_loc = [[1]] # This is the main variable we want to fill, also called
                      # Sigma in other notations or more formally the errors/errata
                      # locator polynomial.
        old_loc = [[1]] # BM is an iterative algorithm, and we need the errata locator
                      # polynomial of the previous iteration in order to updated
                      # other necessary variables.
        new_loc = [[1]]
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
        # delta = gf_poly_mult(err_loc[end:-1:1], synd)[K+1]
        # But this can be optimized: since we only need the kth element, we don't
        # need to compute the polynomial multiplication for any other element but
        # the kth. Thus, to optimize, we compute the poly_mult only at the item
        # we need, skipping the rest (avoiding a nested loop, thus we are linear
        # time instead of quadratic).
        # This optimization is actually described in several figures of the book
        # [Blahut, 2003].
        delta = synd[K+1]
        for j=2:minimum([K+1, length(err_loc)])
            index = (K+2)-j
            delta = gf_add(delta, gf_mult(err_loc[end - j + 1], synd[index])) 
                                    # delta is also called
                                    # discrepancy. Here we do a partial polynomial
                                    # multiplication (i.e., we compute the 
                                    # polynomial multiplication only for the term
                                    # of degree K). Should be equivalent to
                                    # brownanrs.polynomials.mul_at().
        end
        # Shift polynomials to compute the next degree
        append!(old_loc, [[0]])
        # Iteratively estimate the errata locator and evaluator polynomials
        if anti_gf_convert(delta) != 0 # Update only if there's a discrepancy
            # Update with the discrepancy
            new_loc = gf_poly_sub(err_loc, gf_poly_scale(old_loc, delta))
            if length(old_loc) > length(err_loc) # Rule B (Rule A is implicitly 
                                    # defined because rule A just says that we skip
                                    # any modification for this iteration
            #if 2*L <= K+erase_count # equivalent to length(old_loc) > length(err_loc),
            #                        # as long as L is correctly computed.
                # Computing errata locator polynomial Sigma
                old_loc = gf_poly_scale(err_loc, gf_inverse(delta))
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
            err_loc = copy(new_loc)
        end
    end
    # println("err_loc_in=",[anti_gf_convert(err_loc[i]) for i in eachindex(err_loc)])

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
        if anti_gf_convert(gf_poly_eval(err_loc, gf_pow(gf_generator,i))) == 0 # it's a 0? Bingo, it's a root
                            # of the error locator polynomial, in other terms is
                            # the location of an error.
            append!(err_pos, [nmess - i])
        end
    end
    # Sanity check: the number of errors/errata positions found should be exactly
    # the same as the length of the errata locator polynomial
    if length(err_pos) != errs # couldn't find error locations
        throw(ReedSolomonError("Too many (or few) errors found by Chien Search for the errata locator polynomial!"))
    end

    return err_pos[end:-1:1]
end

function rs_correct_errata(msg_in, synd, err_pos)
#'''Forney algorithm, computes the values (error magnitudes) to correct the input
#   message.'''

    # calculate errata locator polynomial to correct both errors and erasures (by
    # combining the errors positions given by the error locator polynomial found
    # by BM with the erasures positions given by caller)
    coef_pos = [length(msg_in) - anti_gf_convert(p) for p in err_pos] # need to gf_convert the 
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
        ell = field_charac - coef_pos[i]
        append!(X,[gf_pow(gf_convert(gf_generator),-ell)])
    end

    # Forney algorithm: compute the magnitudes
    E = [[0] for i=1:length(msg_in)]
    # E = zeros(Int, length(msg_in))    # will store the values that need to be 
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
                append!(err_loc_prime_tmp, [gf_sub([1], gf_mult(Xi_inv, X[j]))])
            end
        end
        # compute the product, which is the denominator of the Forney algorithm
        # (errata locator derivative )
        err_loc_prime = [1]
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
        if anti_gf_convert(err_loc_prime) == 0
            throw(ReedSolomonError("Could not find error magnitude"))
        end

        # Compute the magnitude
        magnitude = gf_mult(y, gf_inverse(err_loc_prime)) # magnitude value of the error,
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
    msg_in = gf_poly_sub(msg_in, E) # equivalent to Ci = Ri - Ei where Ci is the
                                    # correct message, Ri the received (senseword)
                                    # message, and Ei the errata # magnitudes 
                                    # (minus is replaced by XOR) since it's 
                                    # equivalent in GF(2^p)). So in fact here we
                                    # subtract from the received message the errors
                                    # magnitude, which logically corrects the value
                                    # to what it should be.
    return msg_in
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

function rs_find_errata_locator(e_pos)
# '''Compute the erasures/errors/errata locator polynomial from the erasures/errors
#    /errata positions (the positions must be relative to the x coefficient, eg:
#    "hello worldxxxxxxxxx" is tampered to "h_ll_ worldxxxxxxxxx" with xxxxxxxxx
#    being the ecc of length n-k=9, here the string positions are [1, 4], but the
#    coefficients are reversed since the ecc characters are placed as the first 
#    coefficients of the polynomial, thus the coefficients of the erased characters
#    are n-1 - [1, 4] = [18, 15] = erasures_loc to be specified as an argument.'''
    e_loc = [[1]] # just to init because we will multiply, so it must be 1 so that
                # the multiplication starts correctly without nulling any term 
    # erasures_loc = product(1 - x*alpha^i) for i in erasures_pos and where alpha
    for i in e_pos
        e_loc = gf_poly_mult(e_loc, gf_poly_sub([[1]], [[gf_pow(gf_generator, i)]; [[0]]]))
    end
    return e_loc
end

function rs_correct_msg(msg_in, nsym; erase_pos=nothing, generator=GEN)
#'''Reed-Solomon main decoding function'''
    L = length(msg_in) 
    if L > field_charac # can't decode, message is too bigger
        throw(ArgumentError("Message is too long ("*string(L)*" when max is "*string(field_charac)*")"))
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
            msg_out[e_pos] = [0]
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
    if maximum([anti_gf_convert(synd[i]) for i=1:nsym+1]) == 0
        return msg_out[1:end-2], msg_out[end-1:end] # no errors
    end

    # compute the Forney syndromes, which hide the erasures from the original
    # syndrome (so that BM will just have to deal with errors, not erasures)
    fsynd = rs_forney_syndromes(synd, erase_pos, length(msg_out), generator)
    # compute the error locator polynomial sing Berlekamp-Massey
    err_loc = rs_find_error_locator(fsynd, nsym, erase_count=length(erase_pos))
    # println("err_loc=",[anti_gf_convert(err_loc[i]) for i in eachindex(err_loc)])
    # locate the message errors using Chien search (or brute-force search)
    err_pos = rs_find_errors(err_loc[end:-1:1], length(msg_out))
    # println("err_pos=",[anti_gf_convert(err_pos[i]) for i in eachindex(err_pos)])
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
    if maximum([anti_gf_convert(synd[i]) for i in eachindex(synd)]) > 0
        throw(ReedSolomonError("Could not correct message"))
    end
    # return the sucessfully decoded message
    return msg_out[1:end-nsym], msg_out[end-nsym+1:end] # also return the corrected
        # ecc block so that the user can check()
end

# generator = 5
# prim_poly_47_30 = zeros(Int,31)
# prim_poly_47_30[1] = 1
# prim_poly_47_30[30] = 1
# prim_poly_47_30[31] = 32
# prim_poly = 17
prim_poly = 0x11d # prime polinomial for GF(2^8)
# prim_poly = 65581 # prime polinomial for GF(2^16)
# prim_poly = x^32 + x^7 + x^3 + x^2 + 1 = 4294967437
# prim_poly = 285
k = 1
nsym = 2
# poly=zeros(Int,33)
# poly[1] = 1
# poly[26] = 1
# poly[30] = 1
# poly[31] = 1
# poly[33] = 1

# poly = zeros(Int,9)
# poly[1] = 1
# poly[5] = 1
# poly[6] = 1
# poly[7] = 1
# poly[9] = 1

# GF(7^8)
# poly=zeros(Int,9)
# poly[1] = 1
# poly[8] = 1
# poly[9] = 3
# x^8 + x + 3

msg = []
for i=1:k
    append!(msg, i)
end
# msg_encoded = rs_encode_msg(msg, nsym; generator=7, prim=7, prim_poly=poly, c_exp=8)
msg_encoded = rs_encode_msg(msg, nsym)
# msg_sent = copy(msg_encoded)
# # Tampering 6 characters of the message (over 9 ecc symbols, so we are above the Singleton Bound)
# # msg_sent[1] = [0]
# # msg_sent[2] = [0]
# msg_sent[3] = [0]
# # msg_sent[4] = [0]
# # msg_sent[5] = [0]
# # msg_sent[6] = [0]
# # msg_sent[7] = [0]
# println("Corrupted:","\n", [anti_gf_convert(msg_sent[i]) for i in eachindex(msg_sent)])
# # Decoding/repairing the corrupted message, by providing the locations of a few erasures, we get below the Singleton Bound
# # Remember that the Singleton Bound is: 2*e+v <= (n-k)
# erase_pos = []
# println("erase_pos=",erase_pos)
# corrected_message, corrected_ecc = rs_correct_msg(msg_sent, nsym, erase_pos=erase_pos)
# println("Repaired: ", "\n", [[anti_gf_convert(corrected_message[i]) for i in eachindex(corrected_message)]; [anti_gf_convert(corrected_ecc[i]) for i in eachindex(corrected_ecc)]])

# synd = rs_calc_syndromes([corrected_message; corrected_ecc], nsym)
# println("synd: ",  "\n", [anti_gf_convert(synd[i]) for i in eachindex(synd)])

