# FunctionTransformations Package
An open-source package for [_Mathematica_](https://www.wolfram.com/mathematica/) providing utilities for transformation and simplification of some special functions.

## Functions
The following functions are defined in `FunctionTransformations` context:
* `PolyLogExpand[expr]` expands out [`PolyLog`](https://reference.wolfram.com/language/ref/PolyLog.html) terms in `expr`.
* `GammaExpand[expr]` expands out [`Gamma`](https://reference.wolfram.com/language/ref/Gamma.html) terms in `expr`.


## Examples
```
Import["https://raw.github.com/VladimirReshetnikov/FunctionTransformations/master/FunctionTransformations.m"]

GammaExpand[Gamma[1/18]]

(* 2^(8/9) 3^(1/6) Csc[π/18] Gamma[2/9] Gamma[1/3] Sin[π/9] Sin[2π/9]/Sqrt[π] *)
```
