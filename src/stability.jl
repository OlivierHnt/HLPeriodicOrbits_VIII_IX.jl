function approximate_Floquet_multipliers(filename::AbstractString)
    x = load(filename)["x"]
    return _approximate_Floquet_multipliers(x)
end

function _approximate_Floquet_multipliers(x)
    x_₆₄ = complex.(Float64.(mid.(real.(x))), Float64.(mid.(imag.(x))))
    return eigvals(monodromy(x_₆₄); sortby = abs2)
end

function monodromy(p)
    M = zeros(5, 5)
    tspan = (0.0, 2π)
    for i ∈ 1:5
        u0 = I[1:5,i]
        prob = ODEProblem(vector_field!, u0, tspan, p)
        sol = solve(prob, Tsit5())
        M[:,i] = sol(2π)
    end
    return M
end

function vector_field!(dx, x, p, t)
    u = real.(coefficients(component(p, 1)(t)))
    γ = real(component(p, 2)[1])
    sqrt3 = sqrt(3.0)
    dx[1] = 2γ*(-(4u[3] - u[4] - u[5]) * x[3] + (u[3] + 2(u[4] - u[5])) * x[4] + (u[3] - 2(u[4] - u[5])) * x[5])
    dx[2] = 2γ*sqrt3*((u[5] - u[4]) * x[3] + (2u[4] - u[3]) * x[4] + (u[3] - 2u[5]) * x[5])
    dx[3] = 4γ*(u[3] * x[1] + u[1] * x[3])
    dx[4] = -2γ*(u[4] * x[1] + sqrt3 * u[4] * x[2] + (u[1] + sqrt3 * u[2]) * x[4])
    dx[5] = -2γ*(u[5] * x[1] - sqrt3 * u[5] * x[2] + (u[1] - sqrt3 * u[2]) * x[5])
end
