# HLPeriodicOrbits_VIII_IX.jl

HLPeriodicOrbits_VIII_IX.jl is a Julia package to prove the existence of Bianchi type VIII and IX periodic orbits in Hořava-Lifshitz cosmologies as described in Theorem 4.1 of the paper [Periodic orbits in Hořava-Lifshitz cosmologies](). It also contains the code to approximate the Floquet multipliers of a periodic orbit.

The package exports two functions:
- `prove_periodic_orbit`: returns the interval of existence of the input periodic orbit (cf. folder [data](https://github.com/OlivierHnt/HLPeriodicOrbits_VIII_IX.jl/tree/main/data)) by applying a Newton-Kantorovich argument (cf. Proposition 4.3 of [Periodic orbits in Hořava-Lifshitz cosmologies]()).
- `approximate_Floquet_multipliers`: returns an approximation of the Floquet multipliers of the input periodic orbit (cf. folder [data](https://github.com/OlivierHnt/HLPeriodicOrbits_VIII_IX.jl/tree/main/data)) by integrating the variational equation.

Each file in the folder [data](https://github.com/OlivierHnt/HLPeriodicOrbits_VIII_IX.jl/tree/main/data) contains the following variables (cf. Section 4.1 of [Periodic orbits in Hořava-Lifshitz cosmologies]()):
- `x`: approximation of the desired zero of the mapping ``F``.
- `C₁` (`C\_1<TAB>`): value of the conserved quantity ``\Sigma^2 + \Omega_k``.
- `C₂` (`C\_2<TAB>`): value of the conserved quantity ``N_1 N_2 N_3``.
- `ν` (`\nu<TAB>`): geometric rate of the weighted ``\ell^1`` norm.
- `R`: heuristic radius of the ball containing smaller balls within which ``T`` is a contraction.

## Installation

This package requires [Julia](https://julialang.org) to be installed. To replicate the exact version of the dependencies that was recorded when the computer-assisted proofs were executed, download Julia 1.7.2.

Once this repository has been downloaded, open Julia and execute the following:

```julia
import Pkg
Pkg.activate("path/to/package") # edit the path accordingly
Pkg.instantiate()
```

## Usage

To prove the existence of a periodic orbit and approximate its Floquet multipliers, execute the following:

```julia
using HLPeriodicOrbits_VIII_IX
filename = "data/FILE_NAME" # edit the path accordingly (cf. folder data)
ie = prove_periodic_orbit(filename)
Λ = approximate_Floquet_multipliers(filename)
```
