# Created on September, 2022
# author: AllanEduardo42
# This code is an implementation of Kmsadiqueuzzaman, J & Dey, Sankhanil & Ghosh, 
# Ranjan. (2015). An Algorithm to Find the Irreducible Polynomials Over Galois 
# Field GF(pm). International Journal of Computer Applications. 109. 24-29. 10.5120/19266-1012. 

# ==============================================================================
#                       Find irreducible polynomial
# ==============================================================================

include("RS")
using LinearAlgebra

NREALS = 1
prim = 47
c_exp = 30
generator = 47
field_charac = BigInt(prim)^c_exp-1
N = field_charac ÷ (2^63 - 1)

for r=1:NREALS
    prim_poly = rand(0:prim-1, c_exp-1)
    prim_poly = [1; prim_poly]
    # seen = falses(field_charac+1) # memory variable to indicate if a value was already generated in the field (value at index x is set to 1) or not (set to 0 by default)
    # conflict = false # flag to know if there was at least one conflict

    # # Second loop, build the whole Galois Field
    # gf_exp = [generator]
    # for i = 1:field_charac
    #     # Compute the next value in the field (ie, the next power of alpha/generator)
    #     append!(gf_exp, 0)
    #     result = list(gf_exp) # Copy the result
    #     for i=1:(len(result) - (c_exp-1))
    #         coef = result[i] # precaching
    #         if coef != 0 # log(0) is undefined, so we need to avoid that case explicitly (and it's also a good optimization).
    #             for j=2:c_exp # in synthetic division, we always skip the first coefficient of the divisior,
    #                                               # because it's only used to normalize the result coefficient
    #                 if prim_poly[j] != 0 # log(0) is undefined
    #                     result[i+j-1] = mod_sub(result[i+j-1], mod_mult(prim_poly[j], coef, prim), prim) # equivalent to the more mathematically correct
    #                                                                # (but xoring directly is faster): msg_out[i + j] += -divisor[j] * coef
    #                 end
    #             end
    #         end
    #     end
    
    #     # The resulting msg_out contains both the quotient and the remainder, the remainder being the size of the divisor
    #     # (the remainder has necessarily the same degree as the divisor -- not length but degree == length-1 -- since it's
    #     # what we couldn't divide from the result), so we compute the index where this separation is, and return the quotient and remainder.
    #     separator = length(result) - c_exp + 1
    #     result = result[separator+1:end] # remainder.    

    #     # Rejection criterion: if the value overflowed (above field_charac) or is a duplicate of a previously generated power of alpha, then we reject this polynomial (not prime)
    #     if (length(result) > c_exp) || (seen[value] == true)
    #         conflict = true
    #         break
    #     # Else we flag this value as seen (to maybe detect future duplicates), and we continue onto the next power of alpha
    #     else
    #         seen[value] = true
    #     end
    
    # # End of the second loop: if there's no conflict (no overflow nor duplicated value), this is a prime polynomial!
    # if conflict == false
    #     return poly_prim
    # end
    for i=0:prim-1
        gf_poly_eval()
end
