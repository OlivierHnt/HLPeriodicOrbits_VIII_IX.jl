function prove(filename::AbstractString)
    data = load(filename)
    println("Starting the proof for the periodic orbit ", filename, ":")
    print("  • C₁ = "); showfull(data["C₁"]); print("\n")
    print("  • C₂ = "); showfull(data["C₂"]); print("\n")
    return _prove_periodic_orbit(data["x"], data["C₁"], data["C₂"], data["ν"], data["R"])
end

function _prove_periodic_orbit(x, C₁::Interval{Float64}, C₂::Interval{Float64}, ν::Interval{Float64}, R::Float64)
    n = order(space(space(x)[1]))

    # ensures the numerical approximation satisfies the complex conjugacy symmetry

    x₁, x₂ = component(x, 1), component(x, 2)
    for x₁ⱼ ∈ eachcomponent(x₁)
        x₁ⱼ .= (x₁ⱼ .+ conj.(view(x₁ⱼ, n:-1:-n))) ./ 2
        x₁ⱼ[0] = real(x₁ⱼ[0])
    end
    x₂ .= real.(x₂)

    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(x₁)
    γ = x₂[1]
    s₁, s₂, s₃, s₄, s₅ = sum(Σ₊), sum(Σ₋), sum(N₁), sum(N₂), sum(N₃)

    #

    print("    (i)\n        • R = ", R, " and ν = "); showfull(ν); print("\n")

    space_F = Fourier(2n, 1.0)^5 × ParameterSpace()^3
    F = Sequence(space_F, Vector{Complex{Interval{Float64}}}(undef, dimension(space_F)))
    F!(F, x, C₁, C₂)

    domain_DF = Fourier(3n, 1.0)^5 × ParameterSpace()^3
    DF = LinearOperator(domain_DF, space_F, Matrix{Complex{Interval{Float64}}}(undef, dimension(space_F), dimension(domain_DF)))
    DF!(DF, x, C₁, C₂)

    A = inv(mid.(project(DF, space_F, space_F)))

    X_Fourier = ℓ¹(GeometricWeight(ν))
    X_cartesian_Fourier = NormedCartesianSpace(X_Fourier, ℓ∞())
    X = NormedCartesianSpace((X_cartesian_Fourier, NormedCartesianSpace(ℓ∞(), ℓ∞())), ℓ∞())

    opnorm_A = opnorm(Interval.(A), X)
    bound_tail_A = inv(Interval(2n+1))

    Y = norm(A * F, X)
    print("        • Y = "); showfull(Y); print("\n")

    Z₁ = opnorm(A * DF - I, X) +
        bound_tail_A * opnorm_Df(x, X_Fourier) +
        opnorm_A * inv(ν^(3n+1)) * max(
            1,
            2(abs(s₁) + abs(s₂) + 3(abs(s₃) + abs(s₄) + abs(s₅))),
            abs(s₄)*abs(s₅) + abs(s₃)*abs(s₅) + abs(s₃)*abs(s₄)
            )
    print("        • Z₁ = "); showfull(Z₁); print("\n")

    Z₂ = (opnorm_A + bound_tail_A) *
        (opnorm_∂Σ₊DF(x, R, X_Fourier) + opnorm_∂Σ₋DF(x, R, X_Fourier) +
        opnorm_∂N₁DF(x, R, X_Fourier) + opnorm_∂N₂DF(x, R, X_Fourier) + opnorm_∂N₃DF(x, R, X_Fourier) +
        opnorm_∂γDF(x, R, X_Fourier) + 1)
    print("        • Z₂ = "); showfull(Z₂); print("\n")

    ie = interval_of_existence(Y, Z₁, Z₂, R)
    print("        • interval of existence = "); showfull(ie); print("\n")

    #

    if isempty(ie)
        println("    => (i) failed")
    elseif _prove_periodic_orbit_ii(γ, Σ₊, Σ₋, N₁, N₃, inf(ie), R, X_Fourier)
        println("    => (i) and (ii) succeeded")
    else
        println("    => (i) succeeded and (ii) failed")
    end

    return ie
end

function _prove_periodic_orbit(x, C₁::Interval{BigFloat}, C₂::Interval{BigFloat}, ν::Interval{BigFloat}, R::BigFloat)
    n = order(space(space(x)[1]))

    # ensures the numerical approximation satisfies the complex conjugacy symmetry

    x₁, x₂ = component(x, 1), component(x, 2)
    for x₁ⱼ ∈ eachcomponent(x₁)
        x₁ⱼ .= (x₁ⱼ .+ conj.(view(x₁ⱼ, n:-1:-n))) ./ 2
        x₁ⱼ[0] = real(x₁ⱼ[0])
    end
    x₂ .= real.(x₂)

    # set some variables in interval with lesser precision

    v = coefficients(x)
    x_₆₄ = Sequence(
        space(x),
        complex.(
            Interval.(Float64.(inf.(real.(v)), RoundDown), Float64.(sup.(real.(v)), RoundUp)),
            Interval.(Float64.(inf.(imag.(v)), RoundDown), Float64.(sup.(imag.(v)), RoundUp))
            )
        )
    C₁_₆₄ = Interval(Float64(inf(C₁), RoundDown), Float64(sup(C₁), RoundUp))
    C₂_₆₄ = Interval(Float64(inf(C₂), RoundDown), Float64(sup(C₂), RoundUp))
    ν_₆₄ = Interval(Float64(inf(ν), RoundDown), Float64(sup(ν), RoundUp))
    R_₆₄ = Interval(Float64(R, RoundDown), Float64(R, RoundUp))
    Σ₊_₆₄, Σ₋_₆₄, N₁_₆₄, N₂_₆₄, N₃_₆₄ = eachcomponent(component(x_₆₄, 1))
    γ_₆₄ = component(x_₆₄, 2)[1]
    s₁_₆₄, s₂_₆₄, s₃_₆₄, s₄_₆₄, s₅_₆₄ = sum(Σ₊_₆₄), sum(Σ₋_₆₄), sum(N₁_₆₄), sum(N₂_₆₄), sum(N₃_₆₄)

    #

    print("    (i)\n        • R = ", R, " and ν = "); showfull(ν); print("\n")

    space_F = Fourier(2n, 1.0)^5 × ParameterSpace()^3
    F = Sequence(space_F, Vector{Complex{Interval{BigFloat}}}(undef, dimension(space_F)))
    F!(F, x, C₁, C₂)

    domain_DF = Fourier(3n, 1.0)^5 × ParameterSpace()^3
    DF_₆₄ = LinearOperator(domain_DF, space_F, Matrix{Complex{Interval{Float64}}}(undef, dimension(space_F), dimension(domain_DF)))
    DF!(DF_₆₄, x_₆₄, C₁_₆₄, C₂_₆₄)

    A_₆₄ = inv(mid.(project(DF_₆₄, space_F, space_F)))

    X_Fourier_₆₄ = ℓ¹(GeometricWeight(ν_₆₄))
    X_₆₄ = NormedCartesianSpace((NormedCartesianSpace(X_Fourier_₆₄, ℓ∞()), NormedCartesianSpace(ℓ∞(), ℓ∞())), ℓ∞())
    X_Fourier = ℓ¹(GeometricWeight(ν))
    X = NormedCartesianSpace((NormedCartesianSpace(X_Fourier, ℓ∞()), NormedCartesianSpace(ℓ∞(), ℓ∞())), ℓ∞())

    opnorm_A_₆₄ = opnorm(Interval.(A_₆₄), X_₆₄)
    bound_tail_A_₆₄ = inv(Interval(2n+1))

    Y = norm(A_₆₄ * F, X)
    print("        • Y = "); showfull(Y); print("\n")

    Z₁_₆₄ = opnorm(A_₆₄ * DF_₆₄ - I, X_₆₄) +
        bound_tail_A_₆₄ * opnorm_Df(x_₆₄, X_Fourier_₆₄) +
        opnorm_A_₆₄ * inv(ν_₆₄^(3n+1)) * max(
            1,
            2(abs(s₁_₆₄) + abs(s₂_₆₄) + 3(abs(s₃_₆₄) + abs(s₄_₆₄) + abs(s₅_₆₄))),
            abs(s₄_₆₄)*abs(s₅_₆₄) + abs(s₃_₆₄)*abs(s₅_₆₄) + abs(s₃_₆₄)*abs(s₄_₆₄)
            )
    Z₁ = Interval(BigFloat(inf(Z₁_₆₄), RoundDown), BigFloat(sup(Z₁_₆₄), RoundUp))
    print("        • Z₁ = "); showfull(Z₁); print("\n")

    Z₂_₆₄ = (opnorm_A_₆₄ + bound_tail_A_₆₄) *
        (opnorm_∂Σ₊DF(x_₆₄, R_₆₄, X_Fourier_₆₄) + opnorm_∂Σ₋DF(x_₆₄, R_₆₄, X_Fourier_₆₄) +
        opnorm_∂N₁DF(x_₆₄, R_₆₄, X_Fourier_₆₄) + opnorm_∂N₂DF(x_₆₄, R_₆₄, X_Fourier_₆₄) + opnorm_∂N₃DF(x_₆₄, R_₆₄, X_Fourier_₆₄) +
        opnorm_∂γDF(x_₆₄, R_₆₄, X_Fourier_₆₄) + 1)
    Z₂ = Interval(BigFloat(inf(Z₂_₆₄), RoundDown), BigFloat(sup(Z₂_₆₄), RoundUp))
    print("        • Z₂ = "); showfull(Z₂); print("\n")

    ie = interval_of_existence(Y, Z₁, Z₂, R)
    print("        • interval of existence = "); showfull(ie); print("\n")

    #

    if isempty(ie)
        println("    => (i) failed")
    elseif _prove_periodic_orbit_ii(γ_₆₄, Σ₊_₆₄, Σ₋_₆₄, N₁_₆₄, N₃_₆₄, Float64(inf(ie), RoundUp), R_₆₄, X_Fourier_₆₄)
        println("    => (i) and (ii) succeeded")
    else
        println("    => (i) succeeded and (ii) failed")
    end

    return ie
end

function _prove_periodic_orbit_ii(γ, Σ₊, Σ₋, N₁, N₃, inf_r₀, R, X_Fourier)
    println("    (ii)")
    check_1 = iszero(imag(γ)) & (real(γ) > R)
    println("        • check 1: γ ∈ (0, +∞) -> ", check_1)
    check_2 = check_not_identically_zero(Σ₊, inf_r₀)
    println("        • check 2: Σ₊ is not identically zero in [0, 2π) -> ", check_2)
    check_3 = check_not_identically_zero(N₁, inf_r₀)
    println("        • check 3: N₁ is not identically zero in [0, 2π) -> ", check_3)
    check_4 = check_not_identically_zero(N₃, inf_r₀)
    println("        • check 4: N₃ is not identically zero in [0, 2π) -> ", check_4)
    bound_DN₁ = 4(abs(γ) + inf_r₀) * (norm(Σ₊, X_Fourier) + inf_r₀) * (norm(N₁, X_Fourier) + inf_r₀)
    check_5 = check_no_zeros(N₁, bound_DN₁, inf_r₀, "N₁", "5")
    println("        • check 5: N₁ has no zeros in [0, 2π) -> ", check_5)
    bound_DN₃ = 2(abs(γ) + inf_r₀) * (norm(N₃, X_Fourier) + inf_r₀) * (norm(Σ₊, X_Fourier) + inf_r₀ + sqrt(Interval(3.0))*(norm(Σ₋, X_Fourier) + inf_r₀))
    check_6 = check_no_zeros(N₃, bound_DN₃, inf_r₀, "N₃", "6")
    println("        • check 6: N₃ has no zeros in [0, 2π) -> ", check_6)
    return check_1 & check_2 & check_3 & check_4 & check_5 & check_6
end

#

function F!(F, x, C₁, C₂)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)
    s₁, s₂, s₃, s₄, s₅ = sum(Σ₊), sum(Σ₋), sum(N₁), sum(N₂), sum(N₃)

    F₁, F₂, F₃, F₄, F₅ = eachcomponent(component(F, 1))
    F₆ = component(F, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))
    𝒟 = Derivative(1)

    project!(F₁, 2γ * ((N₂ - N₃) ^ 2 - N₁ * (2N₁ - N₂ - N₃)) + η₁ * Σ₊ - 𝒟(Σ₊))
    project!(F₂, 2γ*sqrt3 * (N₃ - N₂) * (N₁ - N₂ - N₃) - 𝒟(Σ₋))
    project!(F₃, 4γ * (Σ₊ * N₁) - 𝒟(N₁))
    project!(F₄, -2γ * N₂ * (Σ₊ + sqrt3 * Σ₋) + η₂ - 𝒟(N₂))
    project!(F₅, -2γ * N₃ * (Σ₊ - sqrt3 * Σ₋) - 𝒟(N₃))

    F₆[1] = s₁
    F₆[2] = s₁^2 + s₂^2 + s₃^2 + s₄^2 + s₅^2 - 2s₃*s₄ - 2s₃*s₅ - 2s₄*s₅ - C₁
    F₆[3] = s₃*s₄*s₅ - C₂

    return F
end

function DF!(DF, x, C₁, C₂)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)
    s₁, s₂, s₃, s₄, s₅ = sum(Σ₊), sum(Σ₋), sum(N₁), sum(N₂), sum(N₃)

    DF .= zero(eltype(DF))
    M₁₁ = component(DF, 1, 1)
    ∂Σ₊F₁, ∂N₁F₁, ∂N₂F₁, ∂N₃F₁ = component(M₁₁, 1, 1), component(M₁₁, 1, 3), component(M₁₁, 1, 4), component(M₁₁, 1, 5)
    ∂Σ₋F₂, ∂N₁F₂, ∂N₂F₂, ∂N₃F₂ = component(M₁₁, 2, 2), component(M₁₁, 2, 3), component(M₁₁, 2, 4), component(M₁₁, 2, 5)
    ∂Σ₊F₃, ∂N₁F₃ = component(M₁₁, 3, 1), component(M₁₁, 3, 3)
    ∂Σ₊F₄, ∂Σ₋F₄, ∂N₂F₄ = component(M₁₁, 4, 1), component(M₁₁, 4, 2), component(M₁₁, 4, 4)
    ∂Σ₊F₅, ∂Σ₋F₅, ∂N₃F₅ = component(M₁₁, 5, 1), component(M₁₁, 5, 2), component(M₁₁, 5, 5)
    M₁₂ = component(DF, 1, 2)
    DγF₁, DγF₂, DγF₃, DγF₄, DγF₅ = component(M₁₂, 1, 1), component(M₁₂, 2, 1), component(M₁₂, 3, 1), component(M₁₂, 4, 1), component(M₁₂, 5, 1)
    Dη₁F₁ = component(M₁₂, 1, 2)
    Dη₂F₄ = component(M₁₂, 4, 3)
    M₂₁ = component(DF, 2, 1)
    ∂Σ₊F₆, ∂Σ₋F₆, ∂N₁F₆, ∂N₂F₆, ∂N₃F₆ = component(M₂₁, :, 1), component(M₂₁, :, 2), component(M₂₁, :, 3), component(M₂₁, :, 4), component(M₂₁, :, 5)

    sqrt3 = sqrt(3one(real(eltype(x))))
    𝒟 = Derivative(1)

    # F₁ = 2γ * ((N₂ - N₃) ^ 2 - N₁ * (2N₁ - N₂ - N₃)) + η₁ * Σ₊ - 𝒟(Σ₊)
    lsub!(η₁*I, project!(∂Σ₊F₁, 𝒟))
    project!(∂N₁F₁, Multiplication(-2γ * (4N₁ - N₂ - N₃)))
    project!(∂N₂F₁, Multiplication(2γ * (N₁ + 2(N₂ - N₃))))
    project!(∂N₃F₁, Multiplication(2γ * (N₁ - 2(N₂ - N₃))))
    project!(Sequence(codomain(DγF₁), vec(coefficients(DγF₁))), 2((N₂ - N₃) ^ 2 - N₁ * (2N₁ - N₂ - N₃)))
    project!(Sequence(codomain(Dη₁F₁), vec(coefficients(Dη₁F₁))), Σ₊)

    # F₂ = 2γ * sqrt(3) * (N₃ - N₂) * (N₁ - N₂ - N₃) - 𝒟(Σ₋)
    project!(∂Σ₋F₂, 𝒟) .*= -1
    project!(∂N₁F₂, Multiplication(2γ*sqrt3 * (N₃ - N₂)))
    project!(∂N₂F₂, Multiplication(2γ*sqrt3 * (2N₂ - N₁)))
    project!(∂N₃F₂, Multiplication(2γ*sqrt3 * (N₁ - 2N₃)))
    project!(Sequence(codomain(DγF₂), vec(coefficients(DγF₂))), 2sqrt3 * (N₃ - N₂) * (N₁ - N₂ - N₃))

    # F₃ = 4γ * Σ₊ * N₁ - 𝒟(N₁)
    project!(∂Σ₊F₃, Multiplication(4γ * N₁))
    project!(∂N₁F₃, Multiplication(4γ * Σ₊)) .-= project(𝒟, domain(∂N₁F₃), codomain(∂N₁F₃), eltype(DF))
    project!(Sequence(codomain(DγF₃), vec(coefficients(DγF₃))), 4(Σ₊ * N₁))

    # F₄ = -2γ * N₂ * (Σ₊ + sqrt(3) * Σ₋) + η₂ - 𝒟(N₂)
    project!(∂Σ₊F₄, Multiplication(-2γ * N₂))
    project!(∂Σ₋F₄, Multiplication(-2γ*sqrt3 * N₂))
    project!(∂N₂F₄, Multiplication(-2γ * (Σ₊ + sqrt3 * Σ₋))) .-= project(𝒟, domain(∂N₂F₄), codomain(∂N₂F₄), eltype(DF))
    project!(Sequence(codomain(DγF₄), vec(coefficients(DγF₄))), -2N₂ * (Σ₊ + sqrt3 * Σ₋))
    Dη₂F₄[0,1] = one(eltype(DF))

    # F₅ = -2γ * N₃ * (Σ₊ - sqrt(3) * Σ₋) - 𝒟(N₃)
    project!(∂Σ₊F₅, Multiplication(-2γ * N₃))
    project!(∂Σ₋F₅, Multiplication(2γ*sqrt3 * N₃))
    project!(∂N₃F₅, Multiplication(-2γ * (Σ₊ - sqrt3 * Σ₋))) .-= project(𝒟, domain(∂N₃F₅), codomain(∂N₃F₅), eltype(DF))
    project!(Sequence(codomain(DγF₅), vec(coefficients(DγF₅))), -2N₃ * (Σ₊ - sqrt3 * Σ₋))

    # F₆[1] = sum(Σ₊)
    ∂Σ₊F₆[1,:] .= one(eltype(DF))
    # F₆[2] = sum(Σ₊)^2 + sum(Σ₋)^2 + sum(N₁)^2 + sum(N₂)^2 + sum(N₃)^2 - 2sum(N₁)*sum(N₂) - 2sum(N₁)*sum(N₃) - 2sum(N₂)*sum(N₃) - C₁
    ∂Σ₊F₆[2,:] .= 2s₁
    ∂Σ₋F₆[2,:] .= 2s₂
    ∂N₁F₆[2,:] .= 2(s₃ - s₄ - s₅)
    ∂N₂F₆[2,:] .= 2(s₄ - s₃ - s₅)
    ∂N₃F₆[2,:] .= 2(s₅ - s₃ - s₄)
    # F₆[3] = sum(N₁)*sum(N₂)*sum(N₃) - C₂
    ∂N₁F₆[3,:] .= s₄*s₅
    ∂N₂F₆[3,:] .= s₃*s₅
    ∂N₃F₆[3,:] .= s₃*s₄

    return DF
end

#

function opnorm_Df(x, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))

    # f₁ = 2γ * ((N₂ - N₃) ^ 2 - N₁ * (2N₁ - N₂ - N₃)) + η₁ * Σ₊
    v₁ = abs(η₁) + # ∂Σ₊f₁
        2abs(γ) * norm(4N₁ - N₂ - N₃, X_Fourier) + # ∂N₁f₁
        2abs(γ) * norm(N₁ + 2(N₂ - N₃), X_Fourier) + # ∂N₂f₁
        2abs(γ) * norm(N₁ - 2(N₂ - N₃), X_Fourier) # ∂N₃f₁

    # f₂ = 2γ * sqrt(3) * (N₃ - N₂) * (N₁ - N₂ - N₃)
    v₂ = 2abs(γ)*sqrt3 * norm(N₃ - N₂, X_Fourier) + # ∂N₁f₂
        2abs(γ)*sqrt3 * norm(2N₂ - N₁, X_Fourier) + # ∂N₂f₂
        2abs(γ)*sqrt3 * norm(N₁ - 2N₃, X_Fourier) # ∂N₃f₂

    # f₃ = 4γ * Σ₊ * N₁
    v₃ = 4abs(γ) * norm(N₁, X_Fourier) + # ∂Σ₊f₃
        4abs(γ) * norm(Σ₊, X_Fourier) # ∂N₁f₃

    # f₄ = -2γ * N₂ * (Σ₊ + sqrt(3) * Σ₋) + η₂
    v₄ = 2abs(γ) * norm(N₂, X_Fourier) + # ∂Σ₊f₄
        2abs(γ)*sqrt3 * norm(N₂, X_Fourier) + # ∂Σ₋f₄
        2abs(γ) * norm(Σ₊ + sqrt3 * Σ₋, X_Fourier) # ∂N₂f₄

    # f₅ = -2γ * N₃ * (Σ₊ - sqrt(3) * Σ₋)
    v₅ = 2abs(γ) * norm(N₃, X_Fourier) + # ∂Σ₊f₅
        2abs(γ)*sqrt3 * norm(N₃, X_Fourier) + # ∂Σ₋f₅
        2abs(γ) * norm(Σ₊ - sqrt3 * Σ₋, X_Fourier) # ∂N₃f₅

    return max(v₁, v₂, v₃, v₄, v₅)
end

function opnorm_∂Σ₊DF(x, r, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    n_N₁, n_N₂, n_N₃ = norm(N₁, X_Fourier), norm(N₂, X_Fourier), norm(N₃, X_Fourier)

    M₁₁ = 4(abs(γ) + r)
    M₁₂ = max(1, 4(n_N₁ + r), 2(n_N₂ + r), 2(n_N₃ + r))
    M₂₁ = 2

    return max(M₁₁ + M₁₂, M₂₁)
end

function opnorm_∂Σ₋DF(x, r, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))
    n_N₂, n_N₃ = norm(N₂, X_Fourier), norm(N₃, X_Fourier)

    M₁₁ = 2(abs(γ) + r)*sqrt3
    M₁₂ = max(2sqrt3 * (n_N₂ + r), 2sqrt3 * (n_N₃ + r))
    M₂₁ = 2

    return max(M₁₁ + M₁₂, M₂₁)
end

function opnorm_∂N₁DF(x, r, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))
    n_Σ₊ = norm(Σ₊, X_Fourier)
    n_N₁, n_N₂, n_N₃ = norm(N₁, X_Fourier), norm(N₂, X_Fourier), norm(N₃, X_Fourier)

    M₁₁ = 12(abs(γ) + r)
    M₁₂ = max(2(4n_N₁ + n_N₂ + n_N₃ + 6r), 2sqrt3 * (n_N₂ + n_N₃ + 2r), 4(n_Σ₊ + r))
    M₂₁ = max(6, n_N₂ + n_N₃ + 2r)

    return max(M₁₁ + M₁₂, M₂₁)
end

function opnorm_∂N₂DF(x, r, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))
    n_Σ₊, n_Σ₋ = norm(Σ₊, X_Fourier), norm(Σ₋, X_Fourier)
    n_N₁, n_N₂, n_N₃ = norm(N₁, X_Fourier), norm(N₂, X_Fourier), norm(N₃, X_Fourier)

    M₁₁ = 6(abs(γ) + r)*sqrt3
    M₁₂ = max(2(n_N₁ + 2n_N₂ + 2n_N₃ + 5r), 2sqrt3 * (n_N₁ + 2n_N₂ + 3r), 2(n_Σ₊ + r + sqrt3 * (n_Σ₋ + r)))
    M₂₁ = max(6, n_N₁ + n_N₃ + 2r)

    return max(M₁₁ + M₁₂, M₂₁)
end

function opnorm_∂N₃DF(x, r, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))
    n_Σ₊, n_Σ₋ = norm(Σ₊, X_Fourier), norm(Σ₋, X_Fourier)
    n_N₁, n_N₂, n_N₃ = norm(N₁, X_Fourier), norm(N₂, X_Fourier), norm(N₃, X_Fourier)

    M₁₁ = 6(abs(γ) + r)*sqrt3
    M₁₂ = max(2(n_N₁ + 2n_N₂ + 2n_N₃ + 5r), 2sqrt3 * (n_N₁ + 2n_N₃ + 3r), 2(n_Σ₊ + r + sqrt3 * (n_Σ₋ + r)))
    M₂₁ = max(6, n_N₁ + n_N₂ + 2r)

    return max(M₁₁ + M₁₂, M₂₁)
end

function opnorm_∂γDF(x, r, X_Fourier)
    Σ₊, Σ₋, N₁, N₂, N₃ = eachcomponent(component(x, 1))
    γ, η₁, η₂ = component(x, 2)

    sqrt3 = sqrt(3one(real(eltype(x))))
    n_Σ₊, n_Σ₋ = norm(Σ₊, X_Fourier), norm(Σ₋, X_Fourier)
    n_N₁, n_N₂, n_N₃ = norm(N₁, X_Fourier), norm(N₂, X_Fourier), norm(N₃, X_Fourier)

    return max(
        2(4n_N₁ + n_N₂ + n_N₃ + 6r) + 4(n_N₁ + 2n_N₂ + 2n_N₃+ 5r),
        2sqrt3 * (2n_N₁ + 3n_N₂ + 3n_N₃ + 8r),
        4(n_Σ₊ + n_N₁ + 2r),
        2(n_N₂ + r) + 2sqrt3 * (n_N₂ + r) + 2(n_Σ₊ + r + sqrt3 * (n_Σ₋ + r)),
        2(n_N₃ + r) + 2sqrt3 * (n_N₃ + r) + 2(n_Σ₊ + r + sqrt3 * (n_Σ₋ + r))
        )
end

#

function check_not_identically_zero(f, r)
    tmp = [f(Interval(0.0))]
    for tⱼ ∈ 0.0:1e-3:2π
        evaluate!(tmp, f, Interval(tⱼ))
        real_f = real(tmp[1])
        if (inf(real_f - r) > 0) || (sup(real_f + r) < 0)
            return true
        end
    end
    return false
end

function check_no_zeros(f, bound_Df, r, name, checknumber)
    π2 = sup(2convert(Interval{Float64}, π))
    tⱼ = Interval(0.0)
    tmp = [f(tⱼ)]
    count = 0
    while tⱼ < π2
        evaluate!(tmp, f, tⱼ)
        real_f = real(tmp[1])
        if (inf(real_f - r) ≤ 0) && (0 ≤ sup(real_f + r))
            return false
        else
            tⱼ = Interval(inf(tⱼ + prevfloat(inf((abs(real_f) - r)/bound_Df))))
            count += 1
        end
        if count % 10_000 == 1
            print("        • check ", checknumber, ": ", name, " has no zeros in [0, ", round(inf(tⱼ); digits = 6), ")    \u001b[1000D")
        end
    end
    return true
end
