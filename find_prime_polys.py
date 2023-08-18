#!/usr/bin/env python
# -*- coding: utf-8 -*-

###################################################
### Universal Reed-Solomon Codec
### initially released at Wikiversity
###################################################

################### INIT and stuff ###################

try: # compatibility with Python 3+
    xrange
except NameError:
    xrange = range

class ReedSolomonError(Exception):
    pass

field_charac = int(47**3 - 1)

gf_exp = [0] * (2*field_charac) # For efficiency, gf_exp[] has size 2*GF_SIZE, so that a simple multiplication of two numbers can be resolved without calling % 255. For more infos on how to generate this extended exponentiation table, see paper: "Fast software implementation of finite field operations", Cheng Huang and Lihao Xu, Washington University in St. Louis, Tech. Rep (2003).
gf_log = [0] * field_charac


################### GALOIS FIELD ELEMENTS MATHS ###################

def rwh_primes1(n):
    # http://stackoverflow.com/questions/2068372/fastest-way-to-list-all-primes-below-n-in-python/3035188#3035188
    ''' Returns  a list of primes < n '''
    sieve = [True] * (n//2)
    for i in xrange(3,int(n**0.5)+1,2):
        if sieve[i//2]:
            sieve[i*i//2::i] = [False] * ((n-i*i-1)//(2*i)+1)
    return [2] + [2*i+1 for i in xrange(1,n//2) if sieve[i]]

def primes(n):
    """ Returns  a list of primes < n """
    sieve = [True] * n
    for i in range(3,int(n**0.5)+1,2):
        if sieve[i]:
            sieve[i*i::2*i]=[False]*((n-i*i-1)//(2*i)+1)
    return [2] + [i for i in range(3,n,2) if sieve[i]]

def find_prime_polys(generator=2, c_exp=8, fast_primes=False, single=False):
    '''Compute the list of prime polynomials for the given generator and galois field characteristic exponent.'''
    # fast_primes will output less results but will be significantly faster.
    # single will output the first prime polynomial found, so if all you want is to just find one prime polynomial to generate the LUT for Reed-Solomon to work, then just use that.

    # A prime polynomial (necessarily irreducible) is necessary to reduce the multiplications in the Galois Field, so as to avoid overflows.
    # Why do we need a "prime polynomial"? Can't we just reduce modulo 255 (for GF(2^8) for example)? Because we need the values to be unique.
    # For example: if the generator (alpha) = 2 and c_exp = 8 (GF(2^8) == GF(256)), then the generated Galois Field (0, 1, a, a^1, a^2, ..., a^(p-1)) will be galois field it becomes 0, 1, 2, 4, 8, 16, etc. However, upon reaching 128, the next value will be doubled (ie, next power of 2), which will give 256. Then we must reduce, because we have overflowed above the maximum value of 255. But, if we modulo 255, this will generate 256 == 1. Then 2, 4, 8, 16, etc. giving us a repeating pattern of numbers. This is very bad, as it's then not anymore a bijection (ie, a non-zero value doesn't have a unique index). That's why we can't just modulo 255, but we need another number above 255, which is called the prime polynomial.
    # Why so much hassle? Because we are using precomputed look-up tables for multiplication: instead of multiplying a*b, we precompute alpha^a, alpha^b and alpha^(a+b), so that we can just use our lookup table at alpha^(a+b) and get our result. But just like in our original field we had 0,1,2,...,p-1 distinct unique values, in our "LUT" field using alpha we must have unique distinct values (we don't care that they are different from the original field as long as they are unique and distinct). That's why we need to avoid duplicated values, and to avoid duplicated values we need to use a prime irreducible polynomial.

    # Here is implemented a bruteforce approach to find all these prime polynomials, by generating every possible prime polynomials (ie, every integers between field_charac+1 and field_charac*2), and then we build the whole Galois Field, and we reject the candidate prime polynomial if it duplicates even one value or if it generates a value above field_charac (ie, cause an overflow).
    # Note that this algorithm is slow if the field is too big (above 12), because it's an exhaustive search algorithm. There are probabilistic approaches, and almost surely prime approaches, but there is no determistic polynomial time algorithm to find irreducible monic polynomials. More info can be found at: http://people.mpi-inf.mpg.de/~csaha/lectures/lec9.pdf
    # Another faster algorithm may be found at Adleman, Leonard M., and Hendrik W. Lenstra. "Finding irreducible polynomials over finite fields." Proceedings of the eighteenth annual ACM symposium on Theory of computing. ACM, 1986.

    # Prepare the finite field characteristic (2^p - 1), this also represent the maximum possible value in this field
    root_charac = generator # we're in GF(2)
    field_charac = int(root_charac**c_exp - 1)
    field_charac_next = int(root_charac**(c_exp+1) - 1)
    gen = convert(generator, generator)

    prim_candidates = []
    if fast_primes:
        prim_candidates = rwh_primes1(field_charac_next) # generate maybe prime polynomials and check later if they really are irreducible
        prim_candidates = [x for x in prim_candidates if x > field_charac] # filter out too small primes
    else:
        prim_candidates = xrange(field_charac+1, field_charac_next, 2) # try each possible prime polynomial, but skip even numbers (because divisible by 2 so necessarily not irreducible)

    # Start of the main loop
    correct_primes = []
    for prim in prim_candidates: # try potential candidates primitive irreducible polys
        prim_converted = convert(prim, generator)
        seen = [0] * (field_charac+1) # memory variable to indicate if a value was already generated in the field (value at index x is set to 1) or not (set to 0 by default)
        conflict = False # flag to know if there was at least one conflict

        # Second loop, build the whole Galois Field
        gf_exp[0] = [1]
        for i in xrange(field_charac):
            # Compute the next value in the field (ie, the next power of alpha/generator)
            gf_exp[i].append(0)
            gf_exp[i+1] = gf_div(gf_exp[i], prim_converted, generator)[1]
            value = anti_convert(gf_exp[i+1], generator)

            # Rejection criterion: if the value overflowed (above field_charac) or is a duplicate of a previously generated power of alpha, then we reject this polynomial (not prime)
            if value > field_charac or seen[value] == 1:
                conflict = True
                break
            # Else we flag this value as seen (to maybe detect future duplicates), and we continue onto the next power of alpha
            else:
                seen[value] = 1

        # End of the second loop: if there's no conflict (no overflow nor duplicated value), this is a prime polynomial!
        if not conflict: 
            correct_primes.append(prim)
            if single: return prim

    # Return the list of all prime polynomials
    return correct_primes # you can use the following to print the hexadecimal representation of each prime polynomial: print [hex(i) for i in correct_primes]

def init_tables(prim=0x11d, generator=2, c_exp=8):
    '''Precompute the logarithm and anti-log tables for faster computation later, using the provided primitive polynomial.
    These tables are used for multiplication/division since addition/substraction are simple XOR operations inside GF of characteristic 2.
    The basic idea is quite simple: since b**(log_b(x), log_b(y)) == x * y given any number b (the base or generator of the logarithm), then we can use any number b to precompute logarithm and anti-log (exponentiation) tables to use for multiplying two numbers x and y.
    That's why when we use a different base/generator number, the log and anti-log tables are drastically different, but the resulting computations are the same given any such tables.
    For more infos, see https://en.wikipedia.org/wiki/Finite_field_arithmetic#Implementation_tricks
    '''
    # generator is the generator number (the "increment" that will be used to walk through the field by multiplication, this must be a prime number). This is basically the base of the logarithm/anti-log tables. Also often noted "alpha" in academic books.
    # prim is the primitive/prime (binary) polynomial and must be irreducible (ie, it can't represented as the product of two smaller polynomials). It's a polynomial in the binary sense: each bit is a coefficient, but in fact it's an integer between field_charac+1 and field_charac*2, and not a list of gf values. The prime polynomial will be used to reduce the overflows back into the range of the Galois Field without duplicating values (all values should be unique). See the function find_prime_polys() and: http://research.swtch.com/field and http://www.pclviewer.com/rs2/galois.html
    # note that the choice of generator or prime polynomial doesn't matter very much: any two finite fields of size p^n have identical structure, even if they give the individual elements different names (ie, the coefficients of the codeword will be different, but the final result will be the same: you can always correct as many errors/erasures with any choice for those parameters). That's why it makes sense to refer to all the finite fields, and all decoders based on Reed-Solomon, of size p^n as one concept: GF(p^n). It can however impact sensibly the speed (because some parameters will generate sparser tables).
    # c_exp is the exponent for the field's characteristic GF(2^c_exp)

    global gf_exp, gf_log, field_charac
    field_charac = int(2**c_exp - 1)
    gf_exp = [0] * (field_charac * 2) # anti-log (exponential) table. The first two elements will always be [GF256int(1), generator]
    gf_log = [0] * (field_charac+1) # log table, log[0] is impossible and thus unused

    # For each possible value in the galois field 2^8, we will pre-compute the logarithm and anti-logarithm (exponential) of this value
    # To do that, we generate the Galois Field F(2^p) by building a list starting with the element 0 followed by the (p-1) successive powers of the generator a : 1, a, a^1, a^2, ..., a^(p-1).
    x = 1
    for i in xrange(field_charac): # we could skip index 255 which is equal to index 0 because of modulo: g^255==g^0 but either way, this does not change the later outputs (ie, the ecc symbols will be the same either way)
        gf_exp[i] = x # compute anti-log for this value and store it in a table
        gf_log[x] = i # compute log at the same time
        x = (x * generator) % 47

        # If you use only generator==2 or a power of 2, you can use the following which is faster than gf_mult_noLUT():
        #x <<= 1 # multiply by 2 (change 1 by another number y to multiply by a power of 2^y)
        #if x & 0x100: # similar to x >= 256, but a lot faster (because 0x100 == 256)
            #x ^= prim # substract the primary polynomial to the current value (instead of 255, so that we get a unique set made of coprime numbers), this is the core of the tables generation

    # Optimization: double the size of the anti-log table so that we don't need to mod 255 to stay inside the bounds (because we will mainly use this table for the multiplication of two GF numbers, no more).
    for i in xrange(field_charac, field_charac * 2):
        gf_exp[i] = gf_exp[i - field_charac]

    return [gf_log, gf_exp]


def convert(x, prim):
    quocient = x // prim
    remainer = x % prim
    coeffs = [remainer]
    while quocient >= prim:
        remainer = quocient % prim
        quocient = quocient // prim
        coeffs.insert(0,remainer)
    coeffs.insert(0,quocient)

    return coeffs


def anti_convert(x, prim):
    r = 0
    for i in range(len(x)):
        r += x[-i-1]*(prim**i)
    return r


def cl_mult(x,y, prim):
    return (x*y) % prim


def cl_add(x,y,prim):
    return (x+y) % prim


def cl_sub(x,y,prim):
    return (x-y) % prim

def cl_inverse(x,prim):
    for i in range(prim):
        N = prim*i + 1
        if N % x == 0:
            x_inv = N // x
            break
    
    return x_inv

def cl_div(x,y, prim):
    y_inv = cl_inverse(y, prim)
    return cl_mult(x,y_inv,prim)


def gf_div(x,y,prim):
    msg_out = list(x) # Copy the dividend
    normalizer = y[0] # precomputing for performance
    for i in range(0, len(x) - (len(y)-1)):
        msg_out[i] = cl_div(msg_out[i], normalizer, prim) # for general polynomial division (when polynomials are non-monic), the usual way of using
                                  # synthetic division is to divide the divisor g(x) with its leading coefficient, but not needed here.
        coef = msg_out[i] # precaching
        if coef != 0: # log(0) is undefined, so we need to avoid that case explicitly (and it's also a good optimization).
            for j in range(1, len(y)): # in synthetic division, we always skip the first coefficient of the divisior,
                                              # because it's only used to normalize the dividend coefficient
                if y[j] != 0: # log(0) is undefined
                    msg_out[i + j] = cl_sub(msg_out[i + j], cl_mult(y[j], coef, prim), prim) # equivalent to the more mathematically correct
                                                               # (but xoring directly is faster): msg_out[i + j] += -divisor[j] * coef

    # The resulting msg_out contains both the quotient and the remainder, the remainder being the size of the divisor
    # (the remainder has necessarily the same degree as the divisor -- not length but degree == length-1 -- since it's
    # what we couldn't divide from the dividend), so we compute the index where this separation is, and return the quotient and remainder.
    separator = -(len(y)-1)
    return msg_out[:separator], msg_out[separator:] # return quotient, remainder.

def gf_mult_noLUT(x, y, poly, c_exp, prim):
    z = [0]*(len(x) + len(y) - 1)
    for i in range(len(x)):
        for j in range(len(y)):
            z[i+j] = cl_add(z[i+j], cl_mult(x[i],y[j],prim), prim)
    if len(z) > c_exp:
        if z[0] > 0:
            quocient, remainder =  gf_div(z, poly, prim)  
            return remainder   
    return z[:c_exp]      
    

correct_primes = find_prime_polys(generator=47, c_exp=10, fast_primes=True, single=True)
print(correct_primes)
# print(convert(correct_primes, 47))
# for i in range(47^3-1):
#     value = anti_convert(gf_exp[i], 47)
# print([hex(i) for i in correct_primes])

# x = 2209*47
# y = 1
# poly = y
# prim = 47
# coef = 3
# x = convert(x, prim) 
# y = convert(y, prim)
# poly = convert(poly, prim)
# print(x)
# print(y)
# print(gf_mult_noLUT(x, y, poly, coef, prim))

# prim = 47
# i_inv = [0]
# for i in range(1,prim):
#     i_inv.append(cl_inverse(i,prim))
#     print("inverse(%i) = %i, because %i*%i mod %i = %i" % (i, i_inv[i], i, i_inv[i], prim,  i*i_inv[i] % prim))

# print(sorted(i_inv))

# prim = 47
# x = 2209
# print(convert(x,prim))
# print(anti_convert(convert(x,prim),prim))

# print(gf_mult_noLUT([1,0,0], [1, 0], [1, 4, 38, 30], 3, 47))