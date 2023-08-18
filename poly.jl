# Created on July, 2022
# author: AllanEduardo42

# ======================================================
#           Reed Solomon coding and decoding
# ======================================================

using Polynomials

x = rand(1:1:100,6)
y = rand(1:1:100, 6)

function poly_eval(coeff,x)
    L = length(coeff)
    val = 0
    for k = 1: L
        val = val + coeff[end-k+1]*x^k
    end
    return val
end

poly = []
for i=1:4
    append!(poly, [fromroots([x[1:i-1]; x[i+1:end]])])
end

a = [y[i]/poly[i](x[i]) for i = 1:4]
poly = a.*poly

polyy = sum(poly)