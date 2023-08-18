
function is_generator(prim, c_exp, generator, prim_poly)

    divisor = prim_poly
    field_charac = Int128(prim)^c_exp - 1
    z = []
    append!(z,[[1]])
    seen = falses(field_charac)

    for i=1:field_charac-1
        if i==field_charac-1
            println("It is a generator!")
            break
        end
        result = [z[end]; 0]
        L1 = length(result)
        L2 = length(prim_poly)
        if L1 >= L2
            dividend = result
            for i = 1:(L1-L2+1)
                coef = dividend[i] # precaching
                if coef != 0 # log(0) is undefined, so we need to avoid that case explicitly (and it's also a good optimization).
                    for j=2:L2 # in synthetic division, we always skip the first coefficient of the divisior,
                                                    # because it's only used to normalize the dividend coefficient
                        if divisor[j] != 0 # log(0) is undefined
                            dividend[i+j-1] = rem(dividend[i+j-1] + (prim- rem(divisor[j]*coef, prim)), prim) # equivalent to the more mathematically correct
                                                                    # (but xoring directly is faster): dividend[i + j] += -divisor[j] * coef
                        end
                    end
                end
            end
            # The resulting dividend contains both the quotient and the remainder, the remainder being the size of the divisor
            # (the remainder has necessarily the same degree as the divisor -- not length but degree == length-1 -- since it's
            # what we couldn't divide from the dividend), so we compute the index where this separation is, and return the quotient and remainder.
            separator = length(dividend) - length(divisor) + 1
            result = dividend[separator+1:end]
        end
        println("result=",result)
        Z = anti_gf_convert(result, generator)
        println("Z=",Z)
        if seen[Z] == true
            println("It is not a generator!")
            break
        else
            seen[Z] = true
        end
        append!(z,[result])
    end
end

function anti_gf_convert(x, base)
    r = Int128(0)
    for i=0:length(x)-1
        r += x[end-i]*(base^i)
    end
    return r
end

function gf_convert(x, base)

    if length(x) > 1
        return x
    end
    quocient = x ÷ base
    remainer = rem(x, base)
    coeffs = [remainer]
    i = 1
    while quocient >= base
        remainer = rem(quocient, base)
        quocient = quocient ÷ base
        prepend!(coeffs,remainer)
        i += 1
    end
    if quocient != 0
        prepend!(coeffs, quocient)
    end

    return coeffs

end

prim = 47
c_exp = 2
generator = 47
prim_poly = zeros(Int128, c_exp+1)
prim_poly[1] = 1
# prim_poly
prim_poly[2] = 45
prim_poly[3] = 5

prim_poly = gf_convert(anti_gf_convert(prim_poly,prim),generator)

is_generator(prim, c_exp, generator, prim_poly)