module HLPeriodicOrbits_VIII_IX

    import JLD2: load

    using RadiiPolynomial
include("proof.jl")
    export prove_periodic_orbit

    import OrdinaryDiffEq: ODEProblem, solve, Tsit5
include("stability.jl")
    export approximate_Floquet_multipliers

end
