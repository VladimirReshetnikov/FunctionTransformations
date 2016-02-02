(* ::Package:: *)

(*
The MIT License (MIT)

Copyright (c) 2016 Vladimir Reshetnikov <v.reshetnikov@gmail.com>

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

BeginPackage["FunctionTransformations`"];

PolyLogExpand::usage = "PolyLogExpand[\!\(\*StyleBox[\"expr\",FontSlant->\"Italic\"]\)] expands out PolyLog terms in \!\(\*StyleBox[\"expr\",FontSlant->\"Italic\"]\).";
GammaExpand::usage = "GammaExpand[\!\(\*StyleBox[\"expr\",FontSlant->\"Italic\"]\)] expands out Gamma terms in \!\(\*StyleBox[\"expr\",FontSlant->\"Italic\"]\).";

Begin["`Private`"];

polyLogRules = Dispatch[{PolyLog[2, -3] -> -Log[3]^2 - 2 PolyLog[2, 1/3], 
 PolyLog[2, -1 - I/2] -> Pi^2/24 - 1/2 Pi ArcTan[2] + 
   1/2 I Pi Log[2] + I ArcTan[2] Log[2] + Log[2]^2/2 - 
   1/4 I Pi Log[5] - 1/2 Log[2] Log[5] - PolyLog[2, 2 I] + 
   1/2 PolyLog[2, 3/4 + I], 
 PolyLog[2, -1 + I/2] -> Pi^2/8 - 1/2 Pi ArcTan[2] - 
   1/2 I Pi Log[2] - I ArcTan[2] Log[2] + Log[2]^2/2 + 
   1/4 I Pi Log[5] + 1/2 Log[2] Log[5] - Log[5]^2/4 + 
   PolyLog[2, 2 I] - 1/2 PolyLog[2, 1/5] + 1/2 PolyLog[2, 3/4 - I], 
 PolyLog[2, -1 - (2 I)/3] -> -8 I Catalan + Pi^2/24 + 
   3/2 I Pi Log[2] - 6 I ArcTan[5] Log[2] + 4 Log[2]^2 - 
   3/2 I Pi Log[3] + 6 I ArcTan[5] Log[3] - 4 Log[2] Log[3] + 
   Log[3]^2 - 2 I ArcTan[5] Log[5] + 4 Log[2] Log[5] + 
   2 Log[3] Log[5] - Log[5]^2 - 3 Log[2] Log[7] - 2 Log[3] Log[7] + (
   3 Log[7]^2)/2 + PolyLog[2, -1 + (2 I)/3] + 6 PolyLog[2, (2 I)/3] + 
   2 PolyLog[2, 5 I] + PolyLog[2, 1/40] - PolyLog[2, 1/14] + 
   2 PolyLog[2, 1/7] - 1/2 PolyLog[2, 16/81] + 4 PolyLog[2, 1/3] - 
   3 PolyLog[2, 2/5] - PolyLog[2, 2/3 - I] + PolyLog[2, 2/3 + I] + 
   1/2 PolyLog[2, 36/49] + PolyLog[2, 1 - (2 I)/3] - 
   PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, -1 - I] -> -I Catalan - Pi^2/16 - 1/4 I Pi Log[2] + 
   1/2 PolyLog[2, 2 I], 
 PolyLog[2, -1 + I] -> 
  I Catalan - (5 Pi^2)/48 + 1/4 I Pi Log[2] - 
   1/2 Log[2] Log[5] + Log[5]^2/8 - 1/2 PolyLog[2, 2 I] + 
   1/4 PolyLog[2, 1/5], 
 PolyLog[2, -(8/9)] -> -(Pi^2/2) - 6 Log[2] Log[3] + 5 Log[3]^2 + 
   6 PolyLog[2, 1/3] + 1/2 PolyLog[2, 64/81], 
 PolyLog[2, -(7/8)] -> -(9/2) Log[2]^2 + 3 Log[2] Log[3] - Log[3]^2/
   2 + 2 Log[2] Log[5] - Log[5]^2/2 + Log[2] Log[7] - Log[3] Log[7] - 
   PolyLog[2, 1/5] - PolyLog[2, 2/7] - PolyLog[2, 1/3] + 
   PolyLog[2, 3/7], 
 PolyLog[2, -(6/7)] -> -(Pi^2/6) - Log[2] Log[7] - Log[3] Log[7] + 
   Log[7]^2 + PolyLog[2, 1/7] + 1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(5/6)] -> -(Pi^2/12) + Log[2]^2/2 + Log[3]^2 + 
   Log[2] Log[5] - Log[5]^2 - PolyLog[2, 1/5] + PolyLog[2, 1/3] - 
   PolyLog[2, 2/5] + 1/2 PolyLog[2, 25/36], 
 PolyLog[2, -(4/5)] -> -(Pi^2/3) - 2 Log[2] Log[3] + Log[3]^2 + 
   Log[5]^2/2 + 2 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5], 
 PolyLog[2, -(7/9)] -> -(Pi^2/6) + 2 Log[3] Log[7] - Log[7]^2 + 
   4 PolyLog[2, 1/3] - 2 PolyLog[2, 3/7], 
 PolyLog[2, -(3/4)] -> -2 Log[2]^2 + 2 Log[2] Log[7] - Log[7]^2/2 - 
   PolyLog[2, 3/7], 
 PolyLog[2, -(3/4) - I/4] -> -2 I Catalan - (37 Pi^2)/96 + 
   3/4 Pi ArcTan[2] + 9/8 I Pi Log[2] - 1/2 I ArcTan[2] Log[2] -
    Log[2]^2/8 - 3/8 I Pi Log[5] + 1/4 Log[2] Log[5] - Log[5]^2/
   8 - 1/2 PolyLog[2, 2 I] - 1/4 PolyLog[2, 1/5] + 
   2 PolyLog[2, 1/2 + I], 
 PolyLog[2, -(3/4) + I/4] -> 
  2 I Catalan - Pi^2/96 + 3/4 Pi ArcTan[2] - 2 ArcTan[2]^2 - 
   9/8 I Pi Log[2] + 1/2 I ArcTan[2] Log[2] - (17 Log[2]^2)/8 + 
   3/8 I Pi Log[5] + 11/4 Log[2] Log[5] - (3 Log[5]^2)/4 + 
   1/2 PolyLog[2, 2 I] - 1/2 PolyLog[2, 1/5] - 2 PolyLog[2, 1/2 + I], 
 PolyLog[2, -(3/4) - (3 I)/4] -> 
  I Catalan - (7 Pi^2)/96 + 3/8 I Pi Log[2] - (9 Log[2]^2)/8 + 
   1/2 I Pi Log[3] + 3 Log[2] Log[3] - 2 Log[3]^2 - 
   3/2 Log[2] Log[5] + (3 Log[5]^2)/8 - 1/2 PolyLog[2, -((8 I)/9)] - 
   3/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] + 3/4 PolyLog[2, 1/5] - 
   2 PolyLog[2, 1/3], 
 PolyLog[2, -(3/4) + (3 I)/4] -> -I Catalan + (3 Pi^2)/32 - 
   3/8 I Pi Log[2] - (9 Log[2]^2)/8 - 1/2 I Pi Log[3] + 
   2 Log[2] Log[3] - Log[3]^2 + Log[2] Log[5] + Log[3] Log[5] - (
   3 Log[5]^2)/4 - 1/2 PolyLog[2, (8 I)/9] + 3/2 PolyLog[2, 2 I] + 
   PolyLog[2, 3 I] - 1/2 PolyLog[2, 1/5] - PolyLog[2, 2/5], 
 PolyLog[2, -(3/4) - I] -> -10 I Catalan + (13 Pi^2)/
   24 + Pi ArcTan[2] - 2 ArcTan[2]^2 - 7/2 I Pi Log[2] - 
   2 I ArcTan[2] Log[2] - (5 Log[2]^2)/2 - 1/2 I Pi Log[3] + 
   2 I ArcTan[2] Log[3] + 2 Log[2] Log[3] - (5 Log[3]^2)/2 - 
   I Pi Log[5] + 6 Log[2] Log[5] + 2 Log[3] Log[5] - (3 Log[5]^2)/
   2 + 3 Log[2] Log[7] + 2 Log[3] Log[7] - (3 Log[7]^2)/2 + 
   2 PolyLog[2, (2 I)/3] + 5 PolyLog[2, 2 I] + 2 PolyLog[2, 3 I] + 
   2 PolyLog[2, 5 I] + PolyLog[2, 8 I] + PolyLog[2, 1/14] - 
   2 PolyLog[2, 1/7] - 1/4 PolyLog[2, 16/81] - PolyLog[2, 1/5] - 
   PolyLog[2, 1/3] - 2 PolyLog[2, 1/3 - I] - PolyLog[2, 2/5] - 
   2 PolyLog[2, 1/2 + I] - 1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(3/4) + I] -> 
  10 I Catalan - (5 Pi^2)/24 + Pi ArcTan[2] + 
   7/2 I Pi Log[2] + 2 I ArcTan[2] Log[2] - 9 Log[2]^2 + 
   1/2 I Pi Log[3] - 2 I ArcTan[2] Log[3] + 13 Log[2] Log[3] - 
   9 Log[3]^2 + I Pi Log[5] - 14 Log[2] Log[5] - Log[3] Log[5] + 
   3 Log[5]^2 + 6 Log[2] Log[7] + 4 Log[3] Log[7] - 3 Log[7]^2 - 
   2 PolyLog[2, (2 I)/3] - 5 PolyLog[2, 2 I] - 2 PolyLog[2, 3 I] - 
   2 PolyLog[2, 5 I] - PolyLog[2, 8 I] - 2 PolyLog[2, 1/40] + 
   2 PolyLog[2, 1/14] - 4 PolyLog[2, 1/7] + 4 PolyLog[2, 1/5] - 
   14 PolyLog[2, 1/3] - 2 PolyLog[2, 1/3 + I] + 4 PolyLog[2, 2/5] + 
   2 PolyLog[2, 1/2 + I] - PolyLog[2, 36/49], 
 PolyLog[2, -(5/7)] -> -Log[2] Log[3] + Log[3]^2/2 - Log[5]^2 + 
   Log[2] Log[7] + Log[5] Log[7] - Log[7]^2/2 + PolyLog[2, 1/7] - 
   PolyLog[2, 1/5] - PolyLog[2, 2/7] + PolyLog[2, 1/3] - 
   PolyLog[2, 2/5], 
 PolyLog[2, -(7/10)] -> Pi^2/6 - (15 Log[2]^2)/2 + 
   12 Log[2] Log[3] - 9 Log[3]^2 - 2 Log[2] Log[5] + (7 Log[5]^2)/2 + 
   Log[2] Log[7] + Log[3] Log[7] - 3 Log[5] Log[7] + Log[7]^2 - 
   PolyLog[2, 1/35] + 2 PolyLog[2, 1/18] - PolyLog[2, 1/7] - 
   PolyLog[2, 25/144] + 5 PolyLog[2, 1/5] + 3 PolyLog[2, 2/7] - 
   14 PolyLog[2, 1/3] + 4 PolyLog[2, 2/5] + PolyLog[2, 3/7] - 
   1/2 PolyLog[2, 64/81], 
 PolyLog[2, -(2/3)] -> -(1/2) Log[3]^2 + Log[3] Log[5] - Log[5]^2/2 - 
   PolyLog[2, 2/5], 
 PolyLog[2, -(2/3) - I/3] -> -5 I Catalan + Pi^2/48 + 
   1/4 Pi ArcTan[2] - 7/4 I Pi Log[2] + 1/2 I ArcTan[2] Log[2] +
    Log[2]^2/4 + 3/4 I Pi Log[3] + Log[2] Log[3] - (5 Log[3]^2)/
   4 - 5/8 I Pi Log[5] + 1/4 Log[2] Log[5] + 1/2 Log[3] Log[5] + 
   Log[5]^2/4 + 3/2 Log[2] Log[7] + Log[3] Log[7] - (3 Log[7]^2)/4 + 
   2 PolyLog[2, (2 I)/3] + PolyLog[2, 2 I] + PolyLog[2, 5 I] + 
   1/2 PolyLog[2, 8 I] + 1/2 PolyLog[2, 1/14] - PolyLog[2, 1/7] - 
   1/8 PolyLog[2, 16/81] - 1/2 PolyLog[2, 1/3] - 
   PolyLog[2, 1/3 - I] + 1/2 PolyLog[2, 2/5] - 1/4 PolyLog[2, 36/49], 
 PolyLog[2, -(2/3) + I/3] -> 
  5 I Catalan - (3 Pi^2)/16 + 1/4 Pi ArcTan[2] + 
   7/4 I Pi Log[2] - 1/2 I ArcTan[2] Log[2] - 4 Log[2]^2 - 
   3/4 I Pi Log[3] + 9/2 Log[2] Log[3] - 2 Log[3]^2 + 
   5/8 I Pi Log[5] - 25/4 Log[2] Log[5] - Log[3] Log[5] + (
   13 Log[5]^2)/8 + 3 Log[2] Log[7] + 2 Log[3] Log[7] - (3 Log[7]^2)/
   2 - 2 PolyLog[2, (2 I)/3] - PolyLog[2, 2 I] - PolyLog[2, 5 I] - 
   1/2 PolyLog[2, 8 I] - PolyLog[2, 1/40] + PolyLog[2, 1/14] - 
   2 PolyLog[2, 1/7] + 1/4 PolyLog[2, 16/81] + 5/4 PolyLog[2, 1/5] - 
   4 PolyLog[2, 1/3] - PolyLog[2, 1/3 + I] + 3 PolyLog[2, 2/5] - 
   1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(2/3) - (2 I)/3] -> 
  I Catalan - (11 Pi^2)/48 + 3/4 I Pi Log[3] - 
   1/2 Log[2] Log[3] + Log[3]^2/2 - Log[2] Log[5] - Log[3] Log[5] + (
   3 Log[5]^2)/4 + 1/2 PolyLog[2, (8 I)/9] - 3/2 PolyLog[2, 2 I] - 
   PolyLog[2, 3 I] + 1/2 PolyLog[2, 1/5] + PolyLog[2, 2/5], 
 PolyLog[2, -(2/3) + (2 I)/3] -> -I Catalan - Pi^2/16 - 
   3/4 I Pi Log[3] - 3/2 Log[2] Log[3] + (3 Log[3]^2)/2 + 
   3/2 Log[2] Log[5] - (3 Log[5]^2)/8 + 1/2 PolyLog[2, -((8 I)/9)] + 
   3/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 3/4 PolyLog[2, 1/5] + 
   2 PolyLog[2, 1/3], 
 PolyLog[2, -(5/8)] -> (3 Pi^2)/4 - 8 Log[2]^2 + 
   10 Log[2] Log[3] - 9 Log[3]^2 - 4 Log[2] Log[5] + 
   2 Log[3] Log[5] + 6 Log[2] Log[7] + 4 Log[3] Log[7] - 3 Log[7]^2 - 
   PolyLog[2, 1/40] + 2 PolyLog[2, 1/14] - 4 PolyLog[2, 1/7] - 
   1/2 PolyLog[2, 16/81] + 2 PolyLog[2, 1/5] - 10 PolyLog[2, 1/3] - 
   PolyLog[2, 2/5] - PolyLog[2, 36/49], 
 PolyLog[2, -(3/5)] -> Pi^2/12 - Log[2] Log[3] - Log[3]^2 + 
   Log[2] Log[5] + Log[3] Log[5] - Log[5]^2/2 + PolyLog[2, 1/5] - 
   2 PolyLog[2, 1/3] - PolyLog[2, 2/5], 
 PolyLog[2, -(4/7)] -> -(Pi^2/2) - (19 Log[2]^2)/2 + 
   3/2 Log[2] Log[3] + (7 Log[3]^2)/4 - 2 Log[2] Log[5] - 
   5/2 Log[3] Log[5] + 2 Log[5]^2 + 6 Log[2] Log[7] + 
   Log[3] Log[7] - (3 Log[7]^2)/2 + PolyLog[2, 1/56] - 
   1/2 PolyLog[2, 1/45] - 3/4 PolyLog[2, 9/64] - PolyLog[2, 1/7] + 
   2 PolyLog[2, 1/5] - PolyLog[2, 2/7] + 13/2 PolyLog[2, 1/3] + 
   5/2 PolyLog[2, 2/5] - PolyLog[2, 3/7] - 1/4 PolyLog[2, 25/36], 
 PolyLog[2, -(5/9)] -> -((5 Pi^2)/12) + 2 Log[2] Log[3] - 
   Log[3]^2 - Log[2] Log[5] + Log[5]^2 - Log[2] Log[7] + 
   Log[3] Log[7] - Log[5] Log[7] + Log[7]^2/2 - PolyLog[2, 1/7] + 
   PolyLog[2, 2/7] + 2 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5] + 
   PolyLog[2, 3/7], 
 PolyLog[2, -(1/2)] -> -(1/2) Log[2]^2 + Log[2] Log[3] - Log[3]^2/2 - 
   PolyLog[2, 1/3], 
 PolyLog[2, -(1/2) - I/2] -> -I Catalan - Pi^2/32 - 
   1/8 I Pi Log[2] - Log[2]^2/8 + 1/2 Log[2] Log[5] - Log[5]^2/8 + 
   1/2 PolyLog[2, 2 I] - 1/4 PolyLog[2, 1/5], 
 PolyLog[2, -(1/2) + I/2] -> 
  I Catalan - (7 Pi^2)/96 + 1/8 I Pi Log[2] - Log[2]^2/8 - 
   1/2 PolyLog[2, 2 I], 
 PolyLog[2, -(1/2) - (3 I)/4] -> 
  3 I Catalan - (3 Pi^2)/16 + 3/4 Pi ArcTan[2] + 
   1/2 Pi ArcTan[5] - ArcTan[2] ArcTan[5] + 25/8 I Pi Log[2] - 
   5/2 I ArcTan[5] Log[2] - (17 Log[2]^2)/4 + I ArcTan[5] Log[3] + 
   19/4 Log[2] Log[3] - (29 Log[3]^2)/8 + 1/2 I ArcTan[5] Log[5] - 
   7/2 Log[2] Log[5] + 1/4 Log[3] Log[5] + (9 Log[5]^2)/16 + 
   3/4 Log[2] Log[7] + 1/2 Log[3] Log[7] - (3 Log[7]^2)/8 + 
   1/2 PolyLog[2, -1 + (2 I)/3] + PolyLog[2, (2 I)/3] - 
   7/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] - 1/2 PolyLog[2, 5 I] - 
   1/2 PolyLog[2, 8 I] - 1/2 PolyLog[2, 1/40] - 
   1/4 PolyLog[2, 1/26] + 1/4 PolyLog[2, 1/14] + 
   1/4 PolyLog[2, 1/13] - 1/2 PolyLog[2, 1/7] - 
   1/16 PolyLog[2, 16/81] + 7/8 PolyLog[2, 1/5] - 
   19/4 PolyLog[2, 1/3] - 1/2 PolyLog[2, 1/3 - I] - 
   1/2 PolyLog[2, 1/3 + I] + 3/4 PolyLog[2, 2/5] - 
   1/2 PolyLog[2, 2/3 - I] - PolyLog[2, 2/3 + I] - 
   1/8 PolyLog[2, 36/49] - 1/4 PolyLog[2, 1 - (2 I)/3] - 
   1/4 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, -(1/2) + (3 I)/4] -> -7 I Catalan + Pi^2/48 + 
   3/4 Pi ArcTan[2] + 1/2 Pi ArcTan[5] - ArcTan[2] ArcTan[5] - 
   19/8 I Pi Log[2] - 1/2 I ArcTan[5] Log[2] - 
   3/4 I Pi Log[3] + 2 I ArcTan[5] Log[3] - 5/4 Log[2] Log[3] + (
   3 Log[3]^2)/8 - 3/2 I ArcTan[5] Log[5] + 13/2 Log[2] Log[5] + 
   5/4 Log[3] Log[5] - (23 Log[5]^2)/16 - 3/4 Log[2] Log[7] - 
   1/2 Log[3] Log[7] + (3 Log[7]^2)/8 + 
   1/2 PolyLog[2, -1 + (2 I)/3] + 2 PolyLog[2, (2 I)/3] + 
   7/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] + 3/2 PolyLog[2, 5 I] + 
   1/2 PolyLog[2, 8 I] + 1/2 PolyLog[2, 1/40] - 
   1/4 PolyLog[2, 1/26] - 1/4 PolyLog[2, 1/14] + 
   1/4 PolyLog[2, 1/13] + 1/2 PolyLog[2, 1/7] - 
   1/16 PolyLog[2, 16/81] - 17/8 PolyLog[2, 1/5] + 
   9/4 PolyLog[2, 1/3] - 1/2 PolyLog[2, 1/3 - I] - 
   1/2 PolyLog[2, 1/3 + I] - 5/4 PolyLog[2, 2/5] - 
   3/2 PolyLog[2, 2/3 - I] + 1/8 PolyLog[2, 36/49] + 
   1/4 PolyLog[2, 1 - (2 I)/3] - 3/4 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, -(1/2) - I] -> 
  5 I Catalan - (5 Pi^2)/48 + 1/2 Pi ArcTan[2] + 
   7/4 I Pi Log[2] + I ArcTan[2] Log[2] - (9 Log[2]^2)/2 + 
   1/4 I Pi Log[3] - I ArcTan[2] Log[3] + 13/2 Log[2] Log[3] - (
   9 Log[3]^2)/2 + 1/2 I Pi Log[5] - 7 Log[2] Log[5] - 
   1/2 Log[3] Log[5] + (3 Log[5]^2)/2 + 3 Log[2] Log[7] + 
   2 Log[3] Log[7] - (3 Log[7]^2)/2 - PolyLog[2, (2 I)/3] - 
   5/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] - PolyLog[2, 5 I] - 
   1/2 PolyLog[2, 8 I] - PolyLog[2, 1/40] + PolyLog[2, 1/14] - 
   2 PolyLog[2, 1/7] + 2 PolyLog[2, 1/5] - 7 PolyLog[2, 1/3] - 
   PolyLog[2, 1/3 + I] + 2 PolyLog[2, 2/5] - 1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(1/2) + I] -> -5 I Catalan + (5 Pi^2)/48 + 
   1/2 Pi ArcTan[2] - 7/4 I Pi Log[2] - I ArcTan[2] Log[2] - 
   Log[2]^2/4 - 1/4 I Pi Log[3] + I ArcTan[2] Log[3] + 
   Log[2] Log[3] - (5 Log[3]^2)/4 - 1/2 I Pi Log[5] + 
   2 Log[2] Log[5] + Log[3] Log[5] - Log[5]^2/2 + 3/2 Log[2] Log[7] + 
   Log[3] Log[7] - (3 Log[7]^2)/4 + PolyLog[2, (2 I)/3] + 
   5/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] + PolyLog[2, 5 I] + 
   1/2 PolyLog[2, 8 I] + 1/2 PolyLog[2, 1/14] - PolyLog[2, 1/7] - 
   1/8 PolyLog[2, 16/81] - 1/2 PolyLog[2, 1/5] - 1/2 PolyLog[2, 1/3] -
    PolyLog[2, 1/3 - I] - 1/2 PolyLog[2, 2/5] - 1/4 PolyLog[2, 36/49],
  PolyLog[2, -(4/9)] -> -(Pi^2/3) - 2 Log[2] Log[3] + 3 Log[3]^2 - 
   2 Log[3] Log[5] + Log[5]^2 + 1/2 PolyLog[2, 16/81] + 
   2 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5], 
 PolyLog[2, -(3/7)] -> -(Pi^2/4) + Log[2] Log[3] - Log[3] Log[5] + 
   Log[5]^2/2 - Log[2] Log[7] + Log[7]^2/2 + PolyLog[2, 2/7] + 
   PolyLog[2, 2/5] + PolyLog[2, 3/7], 
 PolyLog[2, -(5/12)] -> 
  2 Log[2]^2 + Log[2] Log[3] + Log[3]^2 - Log[5]^2 - Log[2] Log[7] - 
   Log[3] Log[7] + Log[5] Log[7] + PolyLog[2, 1/7] + 
   1/2 PolyLog[2, 25/144] - PolyLog[2, 1/5] - PolyLog[2, 2/7] + 
   PolyLog[2, 1/3] - PolyLog[2, 2/5], 
 PolyLog[2, -(2/5)] -> -(1/2) Log[5]^2 + Log[5] Log[7] - Log[7]^2/2 - 
   PolyLog[2, 2/7], 
 PolyLog[2, -(3/8)] -> Pi^2/12 + (9 Log[2]^2)/2 - Log[2] Log[3] - 
   Log[3]^2 - 2 Log[2] Log[5] + Log[3] Log[5] + 1/2 PolyLog[2, 9/64] +
    PolyLog[2, 1/5] - 2 PolyLog[2, 1/3] - PolyLog[2, 2/5], 
 PolyLog[2, -(1/3)] -> -(Pi^2/6) + Log[3]^2/2 + 2 PolyLog[2, 1/3], 
 PolyLog[2, -(1/3) - (2 I)/3] -> -6 I Catalan - Pi^2/8 + 
   1/2 Pi ArcTan[2] - 2 I ArcTan[2] Log[2] + Log[2]^2/2 - 
   I Pi Log[3] + I ArcTan[2] Log[3] - Log[2] Log[3] + Log[3]^2 - 
   1/4 I Pi Log[5] + 2 Log[2] Log[5] + 3/2 Log[3] Log[5] - (
   5 Log[5]^2)/4 + 3 PolyLog[2, 2 I] + 2 PolyLog[2, 3 I] - 
   3/2 PolyLog[2, 1/5] + 3 PolyLog[2, 1/3] - PolyLog[2, 2/5] + 
   PolyLog[2, 1/2 + I], 
 PolyLog[2, -(1/3) + (2 I)/3] -> 
  6 I Catalan - (7 Pi^2)/24 + 1/2 Pi ArcTan[2] - ArcTan[2]^2 + 
   2 I ArcTan[2] Log[2] - Log[2]^2/2 + I Pi Log[3] - 
   I ArcTan[2] Log[3] + Log[2] Log[3] - Log[3]^2 + 
   1/4 I Pi Log[5] - 2 Log[2] Log[5] - 1/2 Log[3] Log[5] + (
   3 Log[5]^2)/4 - 3 PolyLog[2, 2 I] - 2 PolyLog[2, 3 I] + 
   PolyLog[2, 1/5] - PolyLog[2, 1/3] + PolyLog[2, 2/5] - 
   PolyLog[2, 1/2 + I], 
 PolyLog[2, -(1/3) - I] -> 
  8 I Catalan - Pi^2/6 + 1/2 Pi ArcTan[2] - 2 ArcTan[2]^2 + 
   1/4 I Pi Log[2] + 2 I ArcTan[2] Log[2] - Log[2]^2 + 
   7/4 I Pi Log[3] - I ArcTan[2] Log[3] + 3/2 Log[2] Log[3] - 
   2 Log[3]^2 + 1/4 I Pi Log[5] - 3 Log[2] Log[5] - 
   1/2 Log[3] Log[5] + Log[5]^2 - 5 PolyLog[2, 2 I] - 
   3 PolyLog[2, 3 I] + 2 PolyLog[2, 1/5] - 3 PolyLog[2, 1/3] + 
   PolyLog[2, 2/5] - 2 PolyLog[2, 1/2 + I], 
 PolyLog[2, -(1/3) + I] -> -8 I Catalan + Pi^2/24 + 
   1/2 Pi ArcTan[2] - 1/4 I Pi Log[2] - 2 I ArcTan[2] Log[2] + 
   Log[2]^2 - 7/4 I Pi Log[3] + I ArcTan[2] Log[3] - 
   3/2 Log[2] Log[3] + Log[3]^2 - 1/4 I Pi Log[5] + 
   3 Log[2] Log[5] + 5/2 Log[3] Log[5] - 2 Log[5]^2 + 
   5 PolyLog[2, 2 I] + 3 PolyLog[2, 3 I] - 2 PolyLog[2, 1/5] + 
   3 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5] + 2 PolyLog[2, 1/2 + I], 
 PolyLog[2, -(3/10)] -> -(Pi^2/3) + (7 Log[2]^2)/2 - 
   5 Log[2] Log[3] + 3 Log[3]^2 + 4 Log[2] Log[5] + Log[3] Log[5] - (
   3 Log[5]^2)/2 - 3 Log[2] Log[7] - 2 Log[3] Log[7] + (3 Log[7]^2)/
   2 + PolyLog[2, 1/40] - PolyLog[2, 1/14] + 2 PolyLog[2, 1/7] - 
   PolyLog[2, 1/5] + 6 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5] + 
   1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(2/7)] -> -2 Log[2] Log[3] + Log[2] Log[7] + 
   Log[3] Log[7] - Log[7]^2/2 + PolyLog[2, 1/7] - PolyLog[2, 3/7], 
 PolyLog[2, -(1/4)] -> -2 Log[2]^2 + 2 Log[2] Log[5] - Log[5]^2/2 - 
   PolyLog[2, 1/5], 
 PolyLog[2, -(1/4) - I/4] -> -2 I Catalan + (23 Pi^2)/96 - 
   9/8 I Pi Log[2] - (7 Log[2]^2)/8 + 3/2 Log[2] Log[3] - (
   7 Log[3]^2)/4 + 3/2 Log[2] Log[5] + 1/2 Log[3] Log[5] - (
   5 Log[5]^2)/8 + 3/2 Log[2] Log[7] + Log[3] Log[7] - (3 Log[7]^2)/
   4 + 3/2 PolyLog[2, 2 I] + 1/2 PolyLog[2, 8 I] + 
   1/2 PolyLog[2, 1/14] - PolyLog[2, 1/7] - 1/8 PolyLog[2, 16/81] - 
   3/4 PolyLog[2, 1/5] - 3/2 PolyLog[2, 1/3] - 1/2 PolyLog[2, 2/5] - 
   1/4 PolyLog[2, 36/49], 
 PolyLog[2, -(1/4) + I/4] -> 
  2 I Catalan - (13 Pi^2)/96 + 9/8 I Pi Log[2] - (9 Log[2]^2)/
   8 - 3/2 Log[2] Log[5] + (3 Log[5]^2)/8 - 3/2 PolyLog[2, 2 I] - 
   1/2 PolyLog[2, 8 I] + 3/4 PolyLog[2, 1/5], 
 PolyLog[2, -(2/9)] -> Pi^2/12 - 4 Log[2]^2 + 5/2 Log[2] Log[3] - (
   3 Log[3]^2)/4 + 2 Log[2] Log[5] + 1/2 Log[3] Log[5] - Log[5]^2 + 
   1/2 PolyLog[2, 1/45] - 1/4 PolyLog[2, 9/64] - 2 PolyLog[2, 1/5] - 
   1/2 PolyLog[2, 1/3] - 1/2 PolyLog[2, 2/5] + 1/4 PolyLog[2, 25/36], 
 PolyLog[2, -(1/5)] -> -(Pi^2/12) + Log[2] Log[3] - Log[3]^2/2 - 
   Log[2] Log[5] + Log[5]^2/2 + PolyLog[2, 1/5] - PolyLog[2, 1/3] + 
   PolyLog[2, 2/5], 
 PolyLog[2, -(1/6)] -> -(1/2) Log[2]^2 - Log[2] Log[3] - Log[3]^2/2 + 
   Log[2] Log[7] + Log[3] Log[7] - Log[7]^2/2 - PolyLog[2, 1/7], 
 PolyLog[2, -(1/7)] -> -(Pi^2/4) + Log[3]^2 - Log[3] Log[7] + 
   Log[7]^2/2 + PolyLog[2, 1/7] + 2 PolyLog[2, 1/3] + PolyLog[2, 3/7],
  PolyLog[2, -(1/8)] -> Pi^2/3 - (9 Log[2]^2)/2 + 
   6 Log[2] Log[3] - 3 Log[3]^2 - 6 PolyLog[2, 1/3], 
 PolyLog[2, -(1/9)] -> -(Pi^2/12) - 2 Log[2] Log[3] + 
   2 Log[2] Log[5] + 2 Log[3] Log[5] - (3 Log[5]^2)/2 - 
   PolyLog[2, 1/5] + 4 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5], 
 PolyLog[2, -(1/10)] -> Pi^2/4 + (7 Log[2]^2)/2 - 
   1/2 Log[2] Log[3] - (9 Log[3]^2)/4 - 3 Log[2] Log[5] + 
   3/2 Log[3] Log[5] + Log[5]^2/2 + 1/2 PolyLog[2, 1/45] + 
   1/4 PolyLog[2, 9/64] + PolyLog[2, 1/5] - 11/2 PolyLog[2, 1/3] + 
   1/2 PolyLog[2, 2/5] - 1/4 PolyLog[2, 25/36], 
 PolyLog[2, -(1/12)] -> Pi^2/12 - (3 Log[2]^2)/2 - 
   2 Log[2] Log[3] - Log[3]^2/2 + 3 Log[2] Log[7] + 
   2 Log[3] Log[7] - (3 Log[7]^2)/2 + PolyLog[2, 1/14] - 
   2 PolyLog[2, 1/7] - 1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(I/12)] -> -(Pi^2/24) + I Pi Log[2] - 2 Log[2]^2 + 
   1/2 I Pi Log[3] - 2 Log[2] Log[3] - Log[3]^2/2 - 
   PolyLog[2, 12 I], 
 PolyLog[2, I/12] -> -(Pi^2/24) - I Pi Log[2] - 2 Log[2]^2 - 
   1/2 I Pi Log[3] - 2 Log[2] Log[3] - Log[3]^2/2 - 
   PolyLog[2, -12 I], 
 PolyLog[2, -(I/10)] -> -(Pi^2/24) + 1/2 I Pi Log[2] - Log[2]^2/
   2 + 1/2 I Pi Log[5] - Log[2] Log[5] - Log[5]^2/2 - 
   PolyLog[2, 10 I], 
 PolyLog[2, I/10] -> -(Pi^2/24) - 1/2 I Pi Log[2] - Log[2]^2/
   2 - 1/2 I Pi Log[5] - Log[2] Log[5] - Log[5]^2/2 - 
   PolyLog[2, -10 I], 
 PolyLog[2, -(I/9)] -> -(Pi^2/24) + I Pi Log[3] - 2 Log[3]^2 - 
   PolyLog[2, 9 I], 
 PolyLog[2, I/9] -> -(Pi^2/24) - I Pi Log[3] - 2 Log[3]^2 - 
   PolyLog[2, -9 I], 
 PolyLog[2, -(I/8)] -> -(Pi^2/24) + 3/2 I Pi Log[2] - (
   9 Log[2]^2)/2 - PolyLog[2, 8 I], 
 PolyLog[2, I/8] -> (11 Pi^2)/24 - 3/2 I Pi Log[2] - 
   4 Log[2]^2 + 3 Log[2] Log[3] - (7 Log[3]^2)/2 + 3 Log[2] Log[5] + 
   Log[3] Log[5] - (5 Log[5]^2)/4 + 3 Log[2] Log[7] + 
   2 Log[3] Log[7] - (3 Log[7]^2)/2 + PolyLog[2, 8 I] + 
   PolyLog[2, 1/14] - 2 PolyLog[2, 1/7] - 1/4 PolyLog[2, 16/81] - 
   3/2 PolyLog[2, 1/5] - 3 PolyLog[2, 1/3] - PolyLog[2, 2/5] - 
   1/2 PolyLog[2, 36/49], 
 PolyLog[2, -(I/7)] -> -(Pi^2/24) + 1/2 I Pi Log[7] - Log[7]^2/
   2 - PolyLog[2, 7 I], 
 PolyLog[2, I/7] -> -(Pi^2/4) + Log[3]^2 + 2 Log[2] Log[5] - 
   Log[5]^2/2 - 1/2 I Pi Log[7] - 2 Log[2] Log[7] - 
   Log[3] Log[7] + (3 Log[7]^2)/2 + PolyLog[2, 7 I] + 
   PolyLog[2, 1/7] - PolyLog[2, 1/5] + 2 PolyLog[2, 2/7] + 
   2 PolyLog[2, 1/3] + PolyLog[2, 3/7], 
 PolyLog[2, -(I/6)] -> -(Pi^2/24) + 1/2 I Pi Log[2] - Log[2]^2/
   2 + 1/2 I Pi Log[3] - Log[2] Log[3] - Log[3]^2/2 - 
   PolyLog[2, 6 I], 
 PolyLog[2, I/6] -> -(Pi^2/24) - 1/2 I Pi Log[2] - Log[2]^2/2 - 
   1/2 I Pi Log[3] - Log[2] Log[3] - Log[3]^2/2 - PolyLog[2, -6 I],
  PolyLog[2, -(I/5)] -> -(Pi^2/24) + 1/2 I Pi Log[5] - Log[5]^2/
   2 - PolyLog[2, 5 I], 
 PolyLog[2, I/5] -> -(Pi^2/2) + 4 Log[2]^2 - 7 Log[2] Log[3] + (
   11 Log[3]^2)/2 - 1/2 I Pi Log[5] + 4 Log[2] Log[5] - 
   Log[3] Log[5] - 3 Log[2] Log[7] - 2 Log[3] Log[7] + (3 Log[7]^2)/
   2 + PolyLog[2, 5 I] + PolyLog[2, 1/40] - PolyLog[2, 1/14] + 
   2 PolyLog[2, 1/7] + 1/4 PolyLog[2, 16/81] + 7 PolyLog[2, 1/3] + 
   1/2 PolyLog[2, 36/49], 
 PolyLog[2, -((2 I)/9)] -> -(Pi^2/8) + Log[2]^2/4 - 
   3 Log[2] Log[3] + Log[3]^2 + Log[2] Log[5] + 2 Log[3] Log[5] - (
   5 Log[5]^2)/4 - PolyLog[2, (2 I)/9] + 1/2 PolyLog[2, 1/18] - 
   1/2 PolyLog[2, 1/5] + 4 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5] + 
   1/4 PolyLog[2, 64/81], 
 PolyLog[2, -(I/4)] -> -(Pi^2/24) + I Pi Log[2] - 2 Log[2]^2 - 
   PolyLog[2, 4 I], 
 PolyLog[2, I/4] -> (5 Pi^2)/12 - I Pi Log[2] - (7 Log[2]^2)/
   4 + 7 Log[2] Log[3] - 4 Log[3]^2 + PolyLog[2, 4 I] + 
   1/2 PolyLog[2, 1/18] - 6 PolyLog[2, 1/3] - 1/4 PolyLog[2, 64/81], 
 PolyLog[2, -(I/3)] -> -(Pi^2/24) + 1/2 I Pi Log[3] - Log[3]^2/
   2 - PolyLog[2, 3 I], 
 PolyLog[2, I/3] -> -(1/2) I Pi Log[3] - Log[2] Log[3] + Log[3]^2/
   2 + Log[2] Log[5] + Log[3] Log[5] - (3 Log[5]^2)/4 + 
   PolyLog[2, 3 I] - 1/2 PolyLog[2, 1/5] + 2 PolyLog[2, 1/3] - 
   PolyLog[2, 2/5], 
 PolyLog[2, -((2 I)/5)] -> Pi^2/6 + Log[2]^2/2 + Log[3]^2 + 
   6 Log[2] Log[5] + 2 Log[3] Log[5] - (9 Log[5]^2)/4 - 
   PolyLog[2, (2 I)/5] + PolyLog[2, -12 I] + PolyLog[2, 12 I] + 
   PolyLog[2, 1/30] - 5/2 PolyLog[2, 1/5] + PolyLog[2, 1/3] - 
   PolyLog[2, 2/5], 
 PolyLog[2, -((5 I)/12)] -> -10 I Catalan + Pi^2 - 
   5 I Pi Log[2] - Log[2]^2 + 1/2 I Pi Log[3] + 
   3 Log[2] Log[3] - 6 Log[3]^2 - I Pi Log[5] + 5 Log[2] Log[5] + 
   2 Log[3] Log[5] - Log[5]^2 + 6 Log[2] Log[7] + 4 Log[3] Log[7] - 
   3 Log[7]^2 + 2 PolyLog[2, (2 I)/3] + 6 PolyLog[2, 2 I] + 
   2 PolyLog[2, 5 I] + 2 PolyLog[2, 8 I] + 2 PolyLog[2, 1/14] - 
   4 PolyLog[2, 1/7] - 1/2 PolyLog[2, 16/81] - PolyLog[2, 1/5] - 
   5 PolyLog[2, 1/3] - PolyLog[2, 2/5] - PolyLog[2, 36/49], 
 PolyLog[2, (5 I)/12] -> 
  10 I Catalan + Pi^2/12 + 5 I Pi Log[2] - 10 Log[2]^2 - 
   1/2 I Pi Log[3] + 9 Log[2] Log[3] - 7 Log[3]^2 + 
   I Pi Log[5] - 15 Log[2] Log[5] + 3 Log[5]^2 + 6 Log[2] Log[7] + 
   4 Log[3] Log[7] - 3 Log[7]^2 - 2 PolyLog[2, (2 I)/3] - 
   6 PolyLog[2, 2 I] - 2 PolyLog[2, 5 I] - 2 PolyLog[2, 8 I] - 
   2 PolyLog[2, 1/40] + 2 PolyLog[2, 1/14] - 4 PolyLog[2, 1/7] + 
   5 PolyLog[2, 1/5] - 11 PolyLog[2, 1/3] + 3 PolyLog[2, 2/5] - 
   PolyLog[2, 36/49], 
 PolyLog[2, -(I/2)] -> -(Pi^2/24) + 1/2 I Pi Log[2] - Log[2]^2/
   2 - PolyLog[2, 2 I], 
 PolyLog[2, I/2] -> Pi^2/24 - 1/2 I Pi Log[2] - Log[2]^2/2 + 
   Log[2] Log[5] - Log[5]^2/4 + PolyLog[2, 2 I] - 1/2 PolyLog[2, 1/5],
  PolyLog[2, -((4 I)/7)] -> -(Pi^2/4) - 3 Log[2] Log[3] + (
   5 Log[3]^2)/2 - Log[2] Log[5] - Log[3] Log[5] + (3 Log[5]^2)/4 + 
   Log[2] Log[7] - Log[3] Log[7] + Log[7]^2/2 - PolyLog[2, (4 I)/7] + 
   PolyLog[2, 1/7] + 1/4 PolyLog[2, 16/81] + 1/2 PolyLog[2, 1/5] + 
   PolyLog[2, 2/7] + PolyLog[2, 1/3] + PolyLog[2, 2/5] - 
   PolyLog[2, 3/7] + 1/2 PolyLog[2, 36/49], 
 PolyLog[2, -((3 I)/5)] -> Pi^2/3 - (15 Log[2]^2)/4 + 
   3 Log[2] Log[3] - (11 Log[3]^2)/2 + Log[2] Log[5] + 
   2 Log[3] Log[5] + Log[2] Log[7] + Log[3] Log[7] - Log[5] Log[7] - 
   PolyLog[2, (3 I)/5] + 1/2 PolyLog[2, 1/18] - PolyLog[2, 1/7] - 
   1/2 PolyLog[2, 25/144] + 2 PolyLog[2, 1/5] + PolyLog[2, 2/7] - 
   7 PolyLog[2, 1/3] - 1/4 PolyLog[2, 64/81], 
 PolyLog[2, -((2 I)/3)] -> -(Pi^2/6) - Log[2] Log[3] + (
   3 Log[3]^2)/2 - Log[3] Log[5] + Log[5]^2/2 - PolyLog[2, (2 I)/3] + 
   1/4 PolyLog[2, 16/81] + PolyLog[2, 1/3] + PolyLog[2, 2/5], 
 PolyLog[2, -((3 I)/4)] -> -6 I Catalan + Pi^2/12 - 
   I Pi Log[2] - 2 Log[2]^2 - I Pi Log[3] + (3 Log[3]^2)/2 + 
   4 Log[2] Log[5] - Log[5]^2 + 4 PolyLog[2, 2 I] + 
   2 PolyLog[2, 3 I] - 2 PolyLog[2, 1/5] + 3 PolyLog[2, 1/3], 
 PolyLog[2, (3 I)/4] -> 
  6 I Catalan - Pi^2/3 + I Pi Log[2] - 2 Log[2]^2 + 
   I Pi Log[3] + 2 Log[2] Log[3] - Log[3]^2/2 - 2 Log[2] Log[5] - 
   2 Log[3] Log[5] + (3 Log[5]^2)/2 - 4 PolyLog[2, 2 I] - 
   2 PolyLog[2, 3 I] + PolyLog[2, 1/5] - PolyLog[2, 1/3] + 
   2 PolyLog[2, 2/5], 
 PolyLog[2, -((7 I)/9)] -> -4 I Catalan + (5 Pi^2)/24 - 
   Log[2] Log[3] - (3 Log[3]^2)/2 + 2 Log[2] Log[5] + 
   3 Log[3] Log[5] - 2 Log[5]^2 - 1/2 I Pi Log[7] + 
   2 Log[3] Log[7] - Log[7]^2/2 + PolyLog[2, (4 I)/7] + 
   2 PolyLog[2, (2 I)/3] - 2 PolyLog[2, 2 I] + 2 PolyLog[2, 3 I] + 
   PolyLog[2, 7 I] - 1/4 PolyLog[2, 16/81] - PolyLog[2, 1/5] + 
   3 PolyLog[2, 1/3] - 3 PolyLog[2, 2/5] - 1/2 PolyLog[2, 36/49], 
 PolyLog[2, (7 I)/9] -> 
  4 I Catalan - Pi^2/12 - 4 Log[2] Log[3] + Log[3]^2 - 
   Log[2] Log[5] - 2 Log[3] Log[5] + (5 Log[5]^2)/4 + 
   1/2 I Pi Log[7] + 3 Log[2] Log[7] + 2 Log[3] Log[7] - 
   2 Log[7]^2 - PolyLog[2, (4 I)/7] - 2 PolyLog[2, (2 I)/3] + 
   2 PolyLog[2, 2 I] - 2 PolyLog[2, 3 I] - PolyLog[2, 7 I] + 
   1/2 PolyLog[2, 16/81] + 1/2 PolyLog[2, 1/5] - PolyLog[2, 2/7] + 
   2 PolyLog[2, 2/5] - 2 PolyLog[2, 3/7], 
 PolyLog[2, -((6 I)/7)] -> -((7 Pi^2)/24) + (13 Log[2]^2)/4 - 
   6 Log[2] Log[3] + (7 Log[3]^2)/2 - Log[3] Log[5] - (5 Log[5]^2)/4 +
    Log[3] Log[7] + 2 Log[5] Log[7] - Log[7]^2 - PolyLog[2, (6 I)/7] +
    PolyLog[2, 1/35] - 3/2 PolyLog[2, 1/18] - PolyLog[2, 1/7] + 
   1/2 PolyLog[2, 25/144] - 5/2 PolyLog[2, 1/5] + 7 PolyLog[2, 1/3] - 
   PolyLog[2, 2/5] + 1/4 PolyLog[2, 64/81], 
 PolyLog[2, -2 I] -> -(Pi^2/12) - Log[2] Log[5] + Log[5]^2/4 - 
   PolyLog[2, 2 I] + 1/2 PolyLog[2, 1/5], 
 PolyLog[2, -3 I] -> -(Pi^2/24) + Log[2] Log[3] - Log[3]^2 - 
   Log[2] Log[5] - Log[3] Log[5] + (3 Log[5]^2)/4 - PolyLog[2, 3 I] + 
   1/2 PolyLog[2, 1/5] - 2 PolyLog[2, 1/3] + PolyLog[2, 2/5], 
 PolyLog[2, -4 I] -> -((11 Pi^2)/24) - Log[2]^2/4 - 
   7 Log[2] Log[3] + 4 Log[3]^2 - PolyLog[2, 4 I] - 
   1/2 PolyLog[2, 1/18] + 6 PolyLog[2, 1/3] + 1/4 PolyLog[2, 64/81], 
 PolyLog[2, -5 I] -> (11 Pi^2)/24 - 4 Log[2]^2 + 
   7 Log[2] Log[3] - (11 Log[3]^2)/2 - 4 Log[2] Log[5] + 
   Log[3] Log[5] - Log[5]^2/2 + 3 Log[2] Log[7] + 2 Log[3] Log[7] - (
   3 Log[7]^2)/2 - PolyLog[2, 5 I] - PolyLog[2, 1/40] + 
   PolyLog[2, 1/14] - 2 PolyLog[2, 1/7] - 1/4 PolyLog[2, 16/81] - 
   7 PolyLog[2, 1/3] - 1/2 PolyLog[2, 36/49], 
 PolyLog[2, -7 I] -> (5 Pi^2)/24 - Log[3]^2 - 2 Log[2] Log[5] + 
   Log[5]^2/2 + 2 Log[2] Log[7] + Log[3] Log[7] - 2 Log[7]^2 - 
   PolyLog[2, 7 I] - PolyLog[2, 1/7] + PolyLog[2, 1/5] - 
   2 PolyLog[2, 2/7] - 2 PolyLog[2, 1/3] - PolyLog[2, 3/7], 
 PolyLog[2, -8 I] -> -(Pi^2/2) - Log[2]^2/2 - 3 Log[2] Log[3] + (
   7 Log[3]^2)/2 - 3 Log[2] Log[5] - Log[3] Log[5] + (5 Log[5]^2)/4 - 
   3 Log[2] Log[7] - 2 Log[3] Log[7] + (3 Log[7]^2)/2 - 
   PolyLog[2, 8 I] - PolyLog[2, 1/14] + 2 PolyLog[2, 1/7] + 
   1/4 PolyLog[2, 16/81] + 3/2 PolyLog[2, 1/5] + 3 PolyLog[2, 1/3] + 
   PolyLog[2, 2/5] + 1/2 PolyLog[2, 36/49], 
 PolyLog[2, 1/64] -> (7 Pi^2)/6 - 18 Log[2]^2 + 12 Log[2] Log[3] - 
   8 Log[3]^2 + 6 Log[2] Log[7] + 2 Log[3] Log[7] - 2 Log[7]^2 - 
   2 PolyLog[2, 1/7] - 16 PolyLog[2, 1/3] - 2 PolyLog[2, 3/7], 
 PolyLog[2, 1/50] -> (7 Pi^2)/12 - Log[2]^2/2 - 2 Log[3]^2 - 
   6 Log[2] Log[5] - Log[5]^2 + 6 Log[2] Log[7] + 2 Log[3] Log[7] + 
   4 Log[5] Log[7] - 4 Log[7]^2 - 2 PolyLog[2, 1/7] + 
   2 PolyLog[2, 1/5] - 4 PolyLog[2, 2/7] - 4 PolyLog[2, 1/3] - 
   2 PolyLog[2, 3/7], 
 PolyLog[2, 1/49] -> -(Pi^2/2) + 2 Log[3]^2 - 2 Log[3] Log[7] + 
   Log[7]^2 + 4 PolyLog[2, 1/7] + 4 PolyLog[2, 1/3] + 
   2 PolyLog[2, 3/7], 
 PolyLog[2, 1/36] -> Pi^2/6 - 2 Log[2]^2 - 6 Log[2] Log[3] - 
   Log[3]^2 + 4 Log[2] Log[5] + 2 Log[3] Log[5] - 2 Log[5]^2 + 
   2 Log[2] Log[7] + 2 Log[3] Log[7] - Log[7]^2 - 2 PolyLog[2, 1/7] - 
   2 PolyLog[2, 1/5] + 2 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5], 
 PolyLog[2, 1/28] -> Pi^2/2 - 2 Log[2]^2 + 6 Log[2] Log[3] - 
   4 Log[3]^2 - 2 Log[2] Log[7] + Log[3] Log[7] + 2 PolyLog[2, 1/7] - 
   8 PolyLog[2, 1/3] - PolyLog[2, 3/7], 
 PolyLog[2, 1/27] -> -((7 Pi^2)/12) + Log[2]^2/2 - 
   6 Log[2] Log[3] + 4 Log[3]^2 - 2 Log[3] Log[5] + Log[5]^2 + 
   3 Log[2] Log[7] + 2 Log[3] Log[7] - (3 Log[7]^2)/2 + 
   PolyLog[2, 1/14] - 2 PolyLog[2, 1/7] + 1/2 PolyLog[2, 16/81] + 
   9 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5] - 1/2 PolyLog[2, 36/49], 
 PolyLog[2, 1/25] -> -(Pi^2/6) + 2 Log[2] Log[3] - Log[3]^2 - 
   2 Log[2] Log[5] + Log[5]^2 + 4 PolyLog[2, 1/5] - 
   2 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5], 
 PolyLog[2, 1/21] -> -(Pi^2/3) - Log[2] Log[3] + 2 Log[3]^2 + 
   2 Log[2] Log[5] + Log[3] Log[5] - Log[5]^2 - Log[2] Log[7] - 
   2 Log[3] Log[7] + Log[7]^2 + PolyLog[2, 1/7] - PolyLog[2, 1/5] + 
   PolyLog[2, 2/7] + 5 PolyLog[2, 1/3] - PolyLog[2, 2/5] + 
   PolyLog[2, 3/7], 
 PolyLog[2, 1/16] -> Pi^2/3 - 8 Log[2]^2 + 4 Log[2] Log[3] - 
   2 Log[3]^2 + 4 Log[2] Log[5] - Log[5]^2 - 2 PolyLog[2, 1/5] - 
   4 PolyLog[2, 1/3], 
 PolyLog[2, 1/15] -> -Log[2] Log[5] - Log[3] Log[5] + Log[2] Log[7] + 
   Log[3] Log[7] + Log[5] Log[7] - Log[7]^2 - PolyLog[2, 1/7] + 
   PolyLog[2, 1/5] - PolyLog[2, 2/7] + PolyLog[2, 1/3], 
 PolyLog[2, 1/12] -> Pi^2/3 + 3 Log[2]^2 - 5/2 Log[2] Log[3] - (
   3 Log[3]^2)/4 + 3/2 Log[3] Log[5] - Log[5]^2 + 
   1/2 PolyLog[2, 1/45] + 1/4 PolyLog[2, 9/64] - PolyLog[2, 1/5] - 
   7/2 PolyLog[2, 1/3] - 3/2 PolyLog[2, 2/5] + 1/4 PolyLog[2, 25/36], 
 PolyLog[2, 1/10] -> Pi^2/12 - Log[2]^2/2 + 4 Log[2] Log[3] - 
   2 Log[3]^2 - 3 Log[2] Log[5] + Log[5]^2 + PolyLog[2, 1/5] - 
   4 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5], 
 PolyLog[2, 1/9] -> -(Pi^2/3) + Log[3]^2 + 6 PolyLog[2, 1/3], 
 PolyLog[2, 1/8] -> Pi^2/4 - (9 Log[2]^2)/2 - Log[3]^2 + 
   3 Log[2] Log[7] + Log[3] Log[7] - Log[7]^2 - PolyLog[2, 1/7] - 
   2 PolyLog[2, 1/3] - PolyLog[2, 3/7], 
 PolyLog[2, 1/6] -> Pi^2/12 - Log[2]^2/2 - 2 Log[2] Log[3] + 
   2 Log[2] Log[5] + Log[3] Log[5] - Log[5]^2 - PolyLog[2, 1/5] + 
   PolyLog[2, 1/3] - PolyLog[2, 2/5], 
 PolyLog[2, 2/9] -> 
  2 Log[2] Log[3] - 2 Log[3]^2 - Log[2] Log[7] + Log[3] Log[7] - 
   PolyLog[2, 1/7] + PolyLog[2, 3/7], 
 PolyLog[2, 1/4] -> Pi^2/6 - 2 Log[2]^2 + 2 Log[2] Log[3] - 
   Log[3]^2 - 2 PolyLog[2, 1/3], 
 PolyLog[2, 1/4 - I/4] -> -2 I Catalan + (11 Pi^2)/96 - 
   3/8 I Pi Log[2] - (9 Log[2]^2)/8 + 3/2 Log[2] Log[5] - (
   3 Log[5]^2)/8 + 3/2 PolyLog[2, 2 I] - 3/4 PolyLog[2, 1/5], 
 PolyLog[2, 1/4 + I/4] -> 
  2 I Catalan - Pi^2/96 + 3/8 I Pi Log[2] - (9 Log[2]^2)/8 - 
   3/2 PolyLog[2, 2 I], 
 PolyLog[2, 1/4 - I/2] -> -4 I Catalan + (3 Pi^2)/8 - 
   1/2 Pi ArcTan[2] + 5/4 I Pi Log[2] - 2 I ArcTan[2] Log[2] - 
   2 Log[2]^2 - 1/4 I Pi Log[3] + I ArcTan[2] Log[3] + 
   1/2 Log[2] Log[3] - Log[3]^2 - 1/4 I Pi Log[5] + 
   1/2 Log[2] Log[5] + 3/2 Log[3] Log[5] - (7 Log[5]^2)/8 + 
   PolyLog[2, (2 I)/3] + 1/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 
   1/2 PolyLog[2, 8 I] - 1/4 PolyLog[2, 16/81] + 1/4 PolyLog[2, 1/5] +
    PolyLog[2, 1/3 + I] - 2 PolyLog[2, 2/5], 
 PolyLog[2, 1/4 + I/2] -> 
  4 I Catalan + (3 Pi^2)/8 - 1/2 Pi ArcTan[2] - 
   5/4 I Pi Log[2] + 2 I ArcTan[2] Log[2] - (7 Log[2]^2)/4 + 
   1/4 I Pi Log[3] - I ArcTan[2] Log[3] + 2 Log[2] Log[3] - (
   9 Log[3]^2)/4 + 1/4 I Pi Log[5] + 1/2 Log[2] Log[5] - Log[5]^2/
   8 + 3/2 Log[2] Log[7] + Log[3] Log[7] - (3 Log[7]^2)/4 - 
   PolyLog[2, (2 I)/3] - 1/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] + 
   1/2 PolyLog[2, 8 I] + 1/2 PolyLog[2, 1/14] - PolyLog[2, 1/7] - 
   1/8 PolyLog[2, 16/81] + 1/4 PolyLog[2, 1/5] - 5/2 PolyLog[2, 1/3] +
    PolyLog[2, 1/3 - I] - 1/2 PolyLog[2, 2/5] - 1/4 PolyLog[2, 36/49],
  PolyLog[2, 1/4 - (3 I)/4] -> 
  I Catalan - (7 Pi^2)/96 + 1/4 Pi ArcTan[2] + 
   3/8 I Pi Log[2] + 3/2 I ArcTan[2] Log[2] - (9 Log[2]^2)/8 + 
   3/4 I Pi Log[3] - I ArcTan[2] Log[3] + 3/2 Log[2] Log[3] - 
   Log[3]^2 - 1/8 I Pi Log[5] - 3/4 Log[2] Log[5] - 
   1/2 Log[3] Log[5] + (3 Log[5]^2)/8 - 3/2 PolyLog[2, 2 I] - 
   PolyLog[2, 3 I] + 3/4 PolyLog[2, 1/5] - 2 PolyLog[2, 1/3], 
 PolyLog[2, 1/4 + (3 I)/4] -> -I Catalan + (3 Pi^2)/32 + 
   1/4 Pi ArcTan[2] - 3/8 I Pi Log[2] - 
   3/2 I ArcTan[2] Log[2] - (9 Log[2]^2)/8 - 3/4 I Pi Log[3] + 
   I ArcTan[2] Log[3] + 1/2 Log[2] Log[3] + 1/8 I Pi Log[5] + 
   7/4 Log[2] Log[5] + 1/2 Log[3] Log[5] - (3 Log[5]^2)/4 + 
   3/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 1/2 PolyLog[2, 1/5] - 
   PolyLog[2, 2/5], 
 PolyLog[2, 3/10] -> Pi^2/4 - Log[2]^2/2 - Log[2] Log[3] - 
   Log[2] Log[5] + Log[3] Log[5] - Log[5]^2 + 2 Log[2] Log[7] + 
   Log[5] Log[7] - Log[7]^2 - PolyLog[2, 2/7] - PolyLog[2, 2/5] - 
   PolyLog[2, 3/7], 
 PolyLog[2, 1/3 - I/3] -> -2 I Catalan + Pi^2/8 - 
   1/4 I Pi Log[2] - 1/4 I Pi Log[3] - 1/2 Log[2] Log[3] + 
   Log[2] Log[5] + Log[3] Log[5] - (3 Log[5]^2)/4 + 
   1/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 1/2 PolyLog[2, 1/5] + 
   PolyLog[2, 1/3] - PolyLog[2, 2/5], 
 PolyLog[2, 1/3 + I/3] -> 
  2 I Catalan + Pi^2/24 + 1/4 I Pi Log[2] + 
   1/4 I Pi Log[3] + 1/2 Log[2] Log[3] - Log[3]^2 - 
   1/2 Log[2] Log[5] + Log[5]^2/8 - 1/2 PolyLog[2, 2 I] - 
   PolyLog[2, 3 I] + 1/4 PolyLog[2, 1/5] - PolyLog[2, 1/3], 
 PolyLog[2, 1/3 - I/2] -> -8 I Catalan + (13 Pi^2)/6 - 
   9/2 Pi ArcTan[2] - 7/2 Pi ArcTan[5] + 
   6 ArcTan[2] ArcTan[5] - 15/4 I Pi Log[2] + 
   I ArcTan[5] Log[2] + (15 Log[2]^2)/2 - 1/2 I Pi Log[3] + 
   2 I ArcTan[5] Log[3] - 11 Log[2] Log[3] + (11 Log[3]^2)/2 - 
   I ArcTan[5] Log[5] + 16 Log[2] Log[5] + 2 Log[3] Log[5] - (
   39 Log[5]^2)/8 - 6 Log[2] Log[7] - 4 Log[3] Log[7] + 3 Log[7]^2 - 
   PolyLog[2, -1 + (2 I)/3] + 2 PolyLog[2, (2 I)/3] + 
   5 PolyLog[2, 2 I] + PolyLog[2, 5 I] + PolyLog[2, 8 I] + 
   2 PolyLog[2, 1/40] - 2 PolyLog[2, 1/14] + 4 PolyLog[2, 1/7] - 
   1/2 PolyLog[2, 16/81] - 19/4 PolyLog[2, 1/5] + 
   11 PolyLog[2, 1/3] + 3 PolyLog[2, 1/3 - I] + 
   3 PolyLog[2, 1/3 + I] - 7 PolyLog[2, 2/5] + PolyLog[2, 2/3 - I] + 
   2 PolyLog[2, 2/3 + I] + PolyLog[2, 36/49] - 
   PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 1/3 + I/2] -> 
  16 I Catalan + (4 Pi^2)/3 - 9/2 Pi ArcTan[2] - 
   7/2 Pi ArcTan[5] + 6 ArcTan[2] ArcTan[5] + 9/4 I Pi Log[2] + 
   5 I ArcTan[5] Log[2] - Log[2]^2 + 2 I Pi Log[3] - 
   8 I ArcTan[5] Log[3] - 5 Log[2] Log[3] + (11 Log[3]^2)/2 + 
   3 I ArcTan[5] Log[5] - 2 Log[3] Log[5] - (7 Log[5]^2)/8 - 
   3 Log[2] Log[7] - 2 Log[3] Log[7] + (3 Log[7]^2)/2 - 
   PolyLog[2, -1 + (2 I)/3] - 8 PolyLog[2, (2 I)/3] - 
   5 PolyLog[2, 2 I] - 3 PolyLog[2, 5 I] - PolyLog[2, 8 I] - 
   PolyLog[2, 1/14] + 2 PolyLog[2, 1/7] + 1/2 PolyLog[2, 16/81] - 
   3/4 PolyLog[2, 1/5] + 5 PolyLog[2, 1/3] + 3 PolyLog[2, 1/3 - I] + 
   3 PolyLog[2, 1/3 + I] - PolyLog[2, 2/5] + 3 PolyLog[2, 2/3 - I] + 
   1/2 PolyLog[2, 36/49] - 2 PolyLog[2, 1 - (2 I)/3] + 
   PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 1/3 - (2 I)/3] -> 
  I Catalan - Pi^2/16 - 1/4 Pi ArcTan[2] + 
   3/2 I ArcTan[2] Log[2] + I Pi Log[3] - I ArcTan[2] Log[3] + 
   Log[2] Log[3] - Log[3]^2/2 - 1/8 I Pi Log[5] - 
   7/4 Log[2] Log[5] - 1/2 Log[3] Log[5] + (3 Log[5]^2)/4 - 
   3/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] + 1/2 PolyLog[2, 1/5] + 
   PolyLog[2, 2/5], 
 PolyLog[2, 1/3 + (2 I)/3] -> -I Catalan + (5 Pi^2)/48 - 
   1/4 Pi ArcTan[2] - 3/2 I ArcTan[2] Log[2] - I Pi Log[3] + 
   I ArcTan[2] Log[3] + Log[3]^2/2 + 1/8 I Pi Log[5] + 
   3/4 Log[2] Log[5] + 1/2 Log[3] Log[5] - (3 Log[5]^2)/8 + 
   3/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 3/4 PolyLog[2, 1/5] + 
   2 PolyLog[2, 1/3], 
 PolyLog[2, 3/8] -> -(Pi^2/12) - (9 Log[2]^2)/2 + Log[2] Log[3] + 
   Log[3]^2 + 2 Log[2] Log[5] - Log[3] Log[5] - PolyLog[2, 1/5] + 
   2 PolyLog[2, 1/3] + PolyLog[2, 2/5], 
 PolyLog[2, 2/5 - (3 I)/10] -> -6 I Catalan + (5 Pi^2)/
   12 - Pi ArcTan[2] + (3 ArcTan[2]^2)/2 + 1/2 I Pi Log[2] - 
   3 I ArcTan[2] Log[2] - 3/2 I Pi Log[3] + 2 I ArcTan[2] Log[3] + 
   Log[3]^2/2 - 1/2 I ArcTan[2] Log[5] + 3/2 Log[2] Log[5] + 
   Log[3] Log[5] - (7 Log[5]^2)/8 + 3 PolyLog[2, 2 I] + 
   2 PolyLog[2, 3 I] - PolyLog[2, 1/5] + PolyLog[2, 1/3] - 
   PolyLog[2, 2/5] + PolyLog[2, 1/2 + I], 
 PolyLog[2, 2/5 + (3 I)/10] -> 
  6 I Catalan + Pi^2/4 - Pi ArcTan[2] + ArcTan[2]^2/2 - 
   1/2 I Pi Log[2] + 3 I ArcTan[2] Log[2] - Log[2]^2 + 
   3/2 I Pi Log[3] - 2 I ArcTan[2] Log[3] + 2 Log[2] Log[3] - (
   3 Log[3]^2)/2 + 1/2 I ArcTan[2] Log[5] - 5/2 Log[2] Log[5] - 
   Log[3] Log[5] + (9 Log[5]^2)/8 - 3 PolyLog[2, 2 I] - 
   2 PolyLog[2, 3 I] + 3/2 PolyLog[2, 1/5] - 3 PolyLog[2, 1/3] + 
   PolyLog[2, 2/5] - PolyLog[2, 1/2 + I], 
 PolyLog[2, 5/12] -> -2 Log[2]^2 - Log[2] Log[3] - Log[3]^2 + 
   Log[5]^2 + Log[2] Log[7] + Log[3] Log[7] - Log[5] Log[7] - 
   PolyLog[2, 1/7] + PolyLog[2, 1/5] + PolyLog[2, 2/7] - 
   PolyLog[2, 1/3] + PolyLog[2, 2/5], 
 PolyLog[2, 4/9] -> Pi^2/3 + 2 Log[2] Log[3] - 3 Log[3]^2 + 
   2 Log[3] Log[5] - Log[5]^2 - 2 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5],
  PolyLog[2, 1/2 - I/4] -> -((5 Pi^2)/24) + 1/2 Pi ArcTan[2] + 
   I Pi Log[2] + I ArcTan[2] Log[2] - (3 Log[2]^2)/2 - 
   1/4 I Pi Log[5] - 1/2 Log[2] Log[5] + Log[5]^2/4 - 
   2 PolyLog[2, 2 I] + 1/2 PolyLog[2, 1/5] + PolyLog[2, 1/2 + I], 
 PolyLog[2, 1/2 + I/4] -> Pi^2/8 + 1/2 Pi ArcTan[2] - 
   ArcTan[2]^2 - I Pi Log[2] - I ArcTan[2] Log[2] - (5 Log[2]^2)/
   2 + 1/4 I Pi Log[5] + 5/2 Log[2] Log[5] - Log[5]^2/2 + 
   2 PolyLog[2, 2 I] - 1/2 PolyLog[2, 1/5] - PolyLog[2, 1/2 + I], 
 PolyLog[2, 1/2 - I/3] -> (8 I Catalan)/3 - (11 Pi^2)/36 - 
   1/2 Pi ArcTan[2] + 13/12 Pi ArcTan[5] + 
   2/3 ArcTan[2] ArcTan[5] - ArcTan[5]^2 - 1/2 I Pi Log[2] + 
   2 I ArcTan[5] Log[2] - (17 Log[2]^2)/12 + 1/2 I Pi Log[3] - 
   2 I ArcTan[5] Log[3] - 37/12 Log[2] Log[3] + (7 Log[3]^2)/8 + 
   2/3 I ArcTan[5] Log[5] + 1/6 Log[2] Log[5] - 7/12 Log[3] Log[5] - 
   Log[5]^2/8 + 9/4 Log[2] Log[7] + 3/2 Log[3] Log[7] - (9 Log[7]^2)/
   8 - 2/3 PolyLog[2, -1 + (2 I)/3] - 2 PolyLog[2, (2 I)/3] - 
   2/3 PolyLog[2, 5 I] - 1/6 PolyLog[2, 1/40] - 
   1/12 PolyLog[2, 1/26] + 3/4 PolyLog[2, 1/14] + 
   7/12 PolyLog[2, 1/13] - 3/2 PolyLog[2, 1/7] + 
   11/48 PolyLog[2, 16/81] - 1/2 PolyLog[2, 1/5] + 
   7/12 PolyLog[2, 1/3] + 1/3 PolyLog[2, 1/3 - I] + 
   1/3 PolyLog[2, 1/3 + I] + 5/12 PolyLog[2, 2/5] - 
   PolyLog[2, 1/2 + I/3] + 1/3 PolyLog[2, 2/3 - I] - 
   1/3 PolyLog[2, 2/3 + I] - 3/8 PolyLog[2, 36/49] + 
   5/12 PolyLog[2, 1 - (2 I)/3] + 13/12 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 1/2 - I/2] -> -I Catalan + (5 Pi^2)/96 + 
   1/8 I Pi Log[2] - Log[2]^2/8, 
 PolyLog[2, 1/2 + I/2] -> 
  I Catalan + (5 Pi^2)/96 - 1/8 I Pi Log[2] - Log[2]^2/8, 
 PolyLog[2, 1/2 - (2 I)/3] -> -12 I Catalan - Pi^2/2 + 
   2 Pi ArcTan[2] + I Pi Log[2] - 2 I ArcTan[2] Log[2] + (
   3 Log[2]^2)/2 - 2 I Pi Log[3] + 2 I ArcTan[2] Log[3] - 
   3 Log[2] Log[3] + (3 Log[3]^2)/2 - I Pi Log[5] + 
   3 Log[2] Log[5] + 3 Log[3] Log[5] - 2 Log[5]^2 + 
   4 PolyLog[2, 2 I] + 4 PolyLog[2, 3 I] - 2 PolyLog[2, 1/5] + 
   4 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5] + 4 PolyLog[2, 1/2 + I], 
 PolyLog[2, 1/2 + (2 I)/3] -> 
  12 I Catalan - Pi^2/3 + 2 Pi ArcTan[2] - 4 ArcTan[2]^2 - 
   I Pi Log[2] + 2 I ArcTan[2] Log[2] - (5 Log[2]^2)/2 + 
   2 I Pi Log[3] - 2 I ArcTan[2] Log[3] + Log[2] Log[3] - (
   5 Log[3]^2)/2 + I Pi Log[5] - Log[2] Log[5] - Log[3] Log[5] + 
   Log[5]^2 - 4 PolyLog[2, 2 I] - 4 PolyLog[2, 3 I] + 
   2 PolyLog[2, 1/5] - 4 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5] - 
   4 PolyLog[2, 1/2 + I], 
 PolyLog[2, 1/2 - (3 I)/4] -> Pi^2/24 + I Pi Log[2] - (
   3 Log[2]^2)/2 - 1/2 I Pi Log[3] + 2 Log[2] Log[3] - Log[3]^2/2 -
    PolyLog[2, (2 I)/3] + PolyLog[2, 1/2 + I/3] - 
   PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 1/2 + (3 I)/4] -> (8 I Catalan)/3 - (7 Pi^2)/72 - 
   1/2 Pi ArcTan[2] + 13/12 Pi ArcTan[5] + 
   2/3 ArcTan[2] ArcTan[5] - ArcTan[5]^2 - 3/2 I Pi Log[2] + 
   2 I ArcTan[5] Log[2] - (35 Log[2]^2)/12 + I Pi Log[3] - 
   2 I ArcTan[5] Log[3] - 1/12 Log[2] Log[3] - (9 Log[3]^2)/8 + 
   2/3 I ArcTan[5] Log[5] + 1/6 Log[2] Log[5] + 5/12 Log[3] Log[5] - (
   5 Log[5]^2)/8 + 9/4 Log[2] Log[7] + 3/2 Log[3] Log[7] - (
   9 Log[7]^2)/8 - 2/3 PolyLog[2, -1 + (2 I)/3] - 
   PolyLog[2, (2 I)/3] - 2/3 PolyLog[2, 5 I] - 1/6 PolyLog[2, 1/40] - 
   1/12 PolyLog[2, 1/26] + 3/4 PolyLog[2, 1/14] + 
   7/12 PolyLog[2, 1/13] - 3/2 PolyLog[2, 1/7] - 
   1/48 PolyLog[2, 16/81] - 1/2 PolyLog[2, 1/5] - 
   5/12 PolyLog[2, 1/3] + 1/3 PolyLog[2, 1/3 - I] + 
   1/3 PolyLog[2, 1/3 + I] - 7/12 PolyLog[2, 2/5] - 
   PolyLog[2, 1/2 + I/3] + 1/3 PolyLog[2, 2/3 - I] - 
   1/3 PolyLog[2, 2/3 + I] - 3/8 PolyLog[2, 36/49] - 
   7/12 PolyLog[2, 1 - (2 I)/3] + 13/12 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 1/2 - I] -> Pi^2/6 - ArcTan[2]^2 - Log[2]^2 + 
   Log[2] Log[5] - Log[5]^2/4 - PolyLog[2, 1/2 + I], 
 PolyLog[2, 5/9] -> -(Pi^2/6) + 2 Log[2] Log[3] - Log[3]^2 - 
   2 Log[2] Log[5] + Log[5]^2 + 2 PolyLog[2, 1/3] + 2 PolyLog[2, 2/5],
  PolyLog[2, 4/7] -> Pi^2/6 - 2 Log[2] Log[3] + 2 Log[2] Log[7] + 
   Log[3] Log[7] - Log[7]^2 - PolyLog[2, 3/7], 
 PolyLog[2, 7/12] -> Pi^2/6 - 2 Log[2]^2 - 3 Log[2] Log[3] + 
   2 Log[2] Log[5] + Log[3] Log[5] - Log[5]^2 + Log[2] Log[7] + 
   PolyLog[2, 1/7] - PolyLog[2, 1/5] - PolyLog[2, 2/7] + 
   PolyLog[2, 1/3] - PolyLog[2, 2/5], 
 PolyLog[2, 3/5] -> Pi^2/6 - Log[2] Log[3] + Log[2] Log[5] + 
   Log[3] Log[5] - Log[5]^2 - PolyLog[2, 2/5], 
 PolyLog[2, 5/8] -> Pi^2/4 - (9 Log[2]^2)/2 + 2 Log[2] Log[3] - 
   Log[3]^2 + Log[2] Log[5] + PolyLog[2, 1/5] - 2 PolyLog[2, 1/3] - 
   PolyLog[2, 2/5], 
 PolyLog[2, 2/3] -> Pi^2/6 + Log[2] Log[3] - Log[3]^2 - 
   PolyLog[2, 1/3], 
 PolyLog[2, 2/3 - I/3] -> -2 I Catalan + 1/4 Pi ArcTan[2] - 
   1/2 I ArcTan[2] Log[2] - 1/2 I Pi Log[3] + I ArcTan[2] Log[3] - 
   1/8 I Pi Log[5] + 1/4 Log[2] Log[5] + 1/2 Log[3] Log[5] - 
   Log[5]^2/8 + 1/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 
   1/4 PolyLog[2, 1/5] + PolyLog[2, 1/3], 
 PolyLog[2, 2/3 + I/3] -> 
  2 I Catalan - Pi^2/12 + 1/4 Pi ArcTan[2] + 
   1/2 I ArcTan[2] Log[2] + 1/2 I Pi Log[3] - I ArcTan[2] Log[3] + 
   Log[2] Log[3] - Log[3]^2 + 1/8 I Pi Log[5] - 
   5/4 Log[2] Log[5] - 1/2 Log[3] Log[5] + (3 Log[5]^2)/4 - 
   1/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] + 1/2 PolyLog[2, 1/5] - 
   PolyLog[2, 1/3] + PolyLog[2, 2/5], 
 PolyLog[2, 2/3 - I/2] -> -12 I Catalan + (5 Pi^2)/8 - 
   3 I Pi Log[2] - 2 I ArcTan[2] Log[2] + 3/2 I Pi Log[3] + 
   2 Log[2] Log[3] - (7 Log[3]^2)/2 - 3/2 I Pi Log[5] + 
   2 Log[2] Log[5] + Log[3] Log[5] + Log[5]^2/2 + 3 Log[2] Log[7] + 
   2 Log[3] Log[7] - (3 Log[7]^2)/2 + 3 PolyLog[2, (2 I)/3] + 
   5 PolyLog[2, 2 I] + 2 PolyLog[2, 5 I] + PolyLog[2, 8 I] + 
   PolyLog[2, 1/14] - 2 PolyLog[2, 1/7] - 1/4 PolyLog[2, 16/81] - 
   3 PolyLog[2, 1/3] - 2 PolyLog[2, 1/3 - I] + PolyLog[2, 2/5] - 
   1/2 PolyLog[2, 36/49], 
 PolyLog[2, 2/3 + I/2] -> 
  12 I Catalan + Pi^2/8 + 3 I Pi Log[2] + 
   2 I ArcTan[2] Log[2] - (17 Log[2]^2)/2 - 3/2 I Pi Log[3] + 
   10 Log[2] Log[3] - (13 Log[3]^2)/2 + 3/2 I Pi Log[5] - 
   14 Log[2] Log[5] - Log[3] Log[5] + (7 Log[5]^2)/2 + 
   6 Log[2] Log[7] + 4 Log[3] Log[7] - 3 Log[7]^2 - 
   3 PolyLog[2, (2 I)/3] - 5 PolyLog[2, 2 I] - 2 PolyLog[2, 5 I] - 
   PolyLog[2, 8 I] - 2 PolyLog[2, 1/40] + 2 PolyLog[2, 1/14] - 
   4 PolyLog[2, 1/7] + 1/4 PolyLog[2, 16/81] + 4 PolyLog[2, 1/5] - 
   11 PolyLog[2, 1/3] - 2 PolyLog[2, 1/3 + I] + 5 PolyLog[2, 2/5] - 
   PolyLog[2, 36/49], 
 PolyLog[2, 2/3 - (2 I)/3] -> 
  I Catalan + Pi^2/16 + 3/4 I Pi Log[3] + 3/2 Log[2] Log[3] - (
   3 Log[3]^2)/2 - 3/2 Log[2] Log[5] + (3 Log[5]^2)/8 - 
   3/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] + 3/4 PolyLog[2, 1/5] - 
   2 PolyLog[2, 1/3], 
 PolyLog[2, 2/3 + (2 I)/3] -> -I Catalan + (11 Pi^2)/48 - 
   3/4 I Pi Log[3] + 1/2 Log[2] Log[3] - Log[3]^2/2 + 
   Log[2] Log[5] + Log[3] Log[5] - (3 Log[5]^2)/4 + 
   3/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 1/2 PolyLog[2, 1/5] - 
   PolyLog[2, 2/5], 
 PolyLog[2, 7/10] -> -(Pi^2/12) - Log[2]^2/2 + 2 Log[2] Log[3] - 
   Log[2] Log[5] - Log[2] Log[7] - Log[3] Log[7] + Log[7]^2 + 
   PolyLog[2, 2/7] + PolyLog[2, 2/5] + PolyLog[2, 3/7], 
 PolyLog[2, 5/7] -> Pi^2/6 - Log[2] Log[5] + Log[2] Log[7] + 
   Log[5] Log[7] - Log[7]^2 - PolyLog[2, 2/7], 
 PolyLog[2, 3/4] -> -2 Log[2]^2 + Log[3]^2 + 2 PolyLog[2, 1/3], 
 PolyLog[2, 3/4 - I/4] -> -2 I Catalan + (23 Pi^2)/96 - 
   1/4 Pi ArcTan[2] + 3/8 I Pi Log[2] - 
   3/2 I ArcTan[2] Log[2] - (9 Log[2]^2)/8 - 1/8 I Pi Log[5] + 
   3/4 Log[2] Log[5] + 3/2 PolyLog[2, 2 I], 
 PolyLog[2, 3/4 + I/4] -> 
  2 I Catalan + (11 Pi^2)/96 - 1/4 Pi ArcTan[2] - 
   3/8 I Pi Log[2] + 3/2 I ArcTan[2] Log[2] - (9 Log[2]^2)/8 + 
   1/8 I Pi Log[5] - 3/4 Log[2] Log[5] + (3 Log[5]^2)/8 - 
   3/2 PolyLog[2, 2 I] + 3/4 PolyLog[2, 1/5], 
 PolyLog[2, 3/4 - I/2] -> -2 I Catalan - Pi^2/6 + 
   3/4 Pi ArcTan[2] + 1/2 Pi ArcTan[5] - ArcTan[2] ArcTan[5] + 
   17/8 I Pi Log[2] - 5/2 I ArcTan[5] Log[2] - (17 Log[2]^2)/4 - 
   I Pi Log[3] + I ArcTan[5] Log[3] + 7/4 Log[2] Log[3] - (
   9 Log[3]^2)/8 + 1/2 I ArcTan[5] Log[5] - 1/2 Log[2] Log[5] + 
   5/4 Log[3] Log[5] - (11 Log[5]^2)/16 + 3/4 Log[2] Log[7] + 
   1/2 Log[3] Log[7] - (3 Log[7]^2)/8 - 1/2 PolyLog[2, -1 + (2 I)/3] +
    PolyLog[2, (2 I)/3] + 1/2 PolyLog[2, 2 I] + PolyLog[2, 3 I] - 
   1/2 PolyLog[2, 5 I] - 1/2 PolyLog[2, 8 I] - 1/2 PolyLog[2, 1/40] - 
   1/4 PolyLog[2, 1/26] + 1/4 PolyLog[2, 1/14] + 
   1/4 PolyLog[2, 1/13] - 1/2 PolyLog[2, 1/7] - 
   1/16 PolyLog[2, 16/81] - 5/8 PolyLog[2, 1/5] - 
   3/4 PolyLog[2, 1/3] - 1/2 PolyLog[2, 1/3 - I] - 
   1/2 PolyLog[2, 1/3 + I] - 1/4 PolyLog[2, 2/5] - 
   1/2 PolyLog[2, 2/3 - I] - 1/8 PolyLog[2, 36/49] + 
   3/4 PolyLog[2, 1 - (2 I)/3] - 1/4 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 3/4 + I/2] -> 
  6 I Catalan - (5 Pi^2)/12 + 3/4 Pi ArcTan[2] + 
   1/2 Pi ArcTan[5] - ArcTan[2] ArcTan[5] - 23/8 I Pi Log[2] + 
   11/2 I ArcTan[5] Log[2] - 4 Log[2]^2 + 7/4 I Pi Log[3] - 
   4 I ArcTan[5] Log[3] + 7/4 Log[2] Log[3] - Log[3]^2/8 + 
   1/2 I ArcTan[5] Log[5] - 1/2 Log[2] Log[5] - 7/4 Log[3] Log[5] + (
   13 Log[5]^2)/16 + 9/4 Log[2] Log[7] + 3/2 Log[3] Log[7] - (
   9 Log[7]^2)/8 - 1/2 PolyLog[2, -1 + (2 I)/3] - 
   4 PolyLog[2, (2 I)/3] - 1/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] - 
   1/2 PolyLog[2, 5 I] + 1/2 PolyLog[2, 8 I] - 1/2 PolyLog[2, 1/40] - 
   1/4 PolyLog[2, 1/26] + 3/4 PolyLog[2, 1/14] + 
   1/4 PolyLog[2, 1/13] - 3/2 PolyLog[2, 1/7] + 
   7/16 PolyLog[2, 16/81] - 5/8 PolyLog[2, 1/5] - 
   7/4 PolyLog[2, 1/3] - 1/2 PolyLog[2, 1/3 - I] - 
   1/2 PolyLog[2, 1/3 + I] + 11/4 PolyLog[2, 2/5] + 
   1/2 PolyLog[2, 2/3 - I] - PolyLog[2, 2/3 + I] - 
   3/8 PolyLog[2, 36/49] - 3/4 PolyLog[2, 1 - (2 I)/3] + 
   5/4 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, 3/4 - (3 I)/4] -> 
  I Catalan - (11 Pi^2)/96 + 9/8 I Pi Log[2] - (9 Log[2]^2)/8 + 
   Log[2] Log[3] - Log[2] Log[5] - Log[3] Log[5] + (3 Log[5]^2)/4 - 
   3/2 PolyLog[2, 2 I] - PolyLog[2, 3 I] + 1/2 PolyLog[2, 1/5] + 
   PolyLog[2, 2/5], 
 PolyLog[2, 3/4 + (3 I)/4] -> -I Catalan + (5 Pi^2)/96 - 
   9/8 I Pi Log[2] - (9 Log[2]^2)/8 + Log[3]^2 + 
   3/2 Log[2] Log[5] - (3 Log[5]^2)/8 + 3/2 PolyLog[2, 2 I] + 
   PolyLog[2, 3 I] - 3/4 PolyLog[2, 1/5] + 2 PolyLog[2, 1/3], 
 PolyLog[2, 7/9] -> Pi^2/6 - 2 Log[3]^2 + Log[3] Log[7] + 
   PolyLog[2, 1/7] - PolyLog[2, 3/7], 
 PolyLog[2, 4/5] -> Pi^2/6 + 2 Log[2] Log[5] - Log[5]^2 - 
   PolyLog[2, 1/5], 
 PolyLog[2, 5/6] -> Pi^2/12 - Log[2]^2/2 - Log[3]^2 - 
   Log[2] Log[5] + Log[5]^2 + PolyLog[2, 1/5] - PolyLog[2, 1/3] + 
   PolyLog[2, 2/5], 
 PolyLog[2, 6/7] -> Pi^2/6 + Log[2] Log[7] + Log[3] Log[7] - 
   Log[7]^2 - PolyLog[2, 1/7], 
 PolyLog[2, 7/8] -> -(Pi^2/12) - (9 Log[2]^2)/2 + Log[3]^2 - 
   Log[3] Log[7] + Log[7]^2 + PolyLog[2, 1/7] + 2 PolyLog[2, 1/3] + 
   PolyLog[2, 3/7], 
 PolyLog[2, 8/9] -> Pi^2/2 + 6 Log[2] Log[3] - 5 Log[3]^2 - 
   6 PolyLog[2, 1/3], 
 PolyLog[2, 9/10] -> Pi^2/12 - Log[2]^2/2 - 2 Log[2] Log[3] + 
   2 Log[3]^2 + Log[2] Log[5] + 2 Log[3] Log[5] - 2 Log[5]^2 - 
   PolyLog[2, 1/5] + 4 PolyLog[2, 1/3] - 2 PolyLog[2, 2/5], 
 PolyLog[2, 1 - I/3] -> (7 Pi^2)/24 - 1/2 Pi ArcTan[2] - 
   1/4 I Pi Log[2] + 5/4 I Pi Log[3] - I ArcTan[2] Log[3] + 
   3/2 Log[2] Log[3] - (3 Log[3]^2)/2 - 1/4 I Pi Log[5] - 
   Log[2] Log[5] - 1/2 Log[3] Log[5] + (3 Log[5]^2)/4 - 
   PolyLog[2, 3 I] + 1/2 PolyLog[2, 1/5] - 2 PolyLog[2, 1/3] + 
   PolyLog[2, 2/5], 
 PolyLog[2, 1 + I/3] -> Pi^2/3 - 1/2 Pi ArcTan[2] + 
   1/4 I Pi Log[2] - 5/4 I Pi Log[3] + I ArcTan[2] Log[3] + 
   1/2 Log[2] Log[3] - Log[3]^2/2 + 1/4 I Pi Log[5] + 
   1/2 Log[3] Log[5] + PolyLog[2, 3 I], 
 PolyLog[2, 1 - I/2] -> -(Pi^2/8) + 1/2 Pi ArcTan[2] + 
   1/2 I Pi Log[2] + I ArcTan[2] Log[2] - Log[2]^2/2 - 
   1/4 I Pi Log[5] - 1/2 Log[2] Log[5] + Log[5]^2/4 - 
   PolyLog[2, 2 I] + 1/2 PolyLog[2, 1/5], 
 PolyLog[2, 1 + I/2] -> -(Pi^2/24) + 1/2 Pi ArcTan[2] - 
   1/2 I Pi Log[2] - I ArcTan[2] Log[2] - Log[2]^2/2 + 
   1/4 I Pi Log[5] + 1/2 Log[2] Log[5] + PolyLog[2, 2 I], 
 PolyLog[2, 1 - (3 I)/4] -> -6 I Catalan + (3 Pi^2)/
   4 - Pi ArcTan[2] + I Pi Log[2] - 4 I ArcTan[2] Log[2] - 
   2 Log[2]^2 - 3/2 I Pi Log[3] + 2 I ArcTan[2] Log[3] + Log[3]^2/
   2 - 1/2 I Pi Log[5] + 4 Log[2] Log[5] + Log[3] Log[5] - (
   3 Log[5]^2)/2 + 4 PolyLog[2, 2 I] + 2 PolyLog[2, 3 I] - 
   PolyLog[2, 1/5] + PolyLog[2, 1/3] - 2 PolyLog[2, 2/5], 
 PolyLog[2, 1 + (3 I)/4] -> 
  6 I Catalan + Pi^2/3 - Pi ArcTan[2] - I Pi Log[2] + 
   4 I ArcTan[2] Log[2] - 2 Log[2]^2 + 3/2 I Pi Log[3] - 
   2 I ArcTan[2] Log[3] + 2 Log[2] Log[3] - (3 Log[3]^2)/2 + 
   1/2 I Pi Log[5] - 2 Log[2] Log[5] - Log[3] Log[5] + Log[5]^2 - 
   4 PolyLog[2, 2 I] - 2 PolyLog[2, 3 I] + 2 PolyLog[2, 1/5] - 
   3 PolyLog[2, 1/3], 
 PolyLog[2, 1 - I] -> -I Catalan + Pi^2/16 - 1/4 I Pi Log[2], 
 PolyLog[2, 1 + I] -> I Catalan + Pi^2/16 + 1/4 I Pi Log[2], 
 PolyLog[2, (-1)^(1/6)] -> (2 I Catalan)/3 + (13 Pi^2)/144 - (
   I Pi^2)/(12 Sqrt[3]) + (I PolyGamma[1, 1/3])/(8 Sqrt[3]), 
 PolyLog[2, -(1/2) (-1)^(1/4)] -> (5 Pi^2)/24 - 
   1/2 I Pi Log[2] - (7 Log[2]^2)/8 + 7/2 Log[2] Log[3] - 
   2 Log[3]^2 + 1/2 PolyLog[2, 4 I] + 1/4 PolyLog[2, 1/18] - 
   3 PolyLog[2, 1/3] - 1/8 PolyLog[2, 64/81] - 
   PolyLog[2, 1/2 (-1)^(1/4)], 
 PolyLog[2, -(1/3) (-1)^(1/4)] -> -(Pi^2/48) - 1/2 I Pi Log[3] -
    Log[3]^2 - 1/2 PolyLog[2, -9 I] - PolyLog[2, 1/3 (-1)^(1/4)], 
 PolyLog[2, (-1)^(1/4)] -> (I Catalan)/4 - (I Catalan)/Sqrt[
   2] + (11/192 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, -3 (-1)^(1/3)] -> -(Pi^2/36) - Log[2]^2/6 + 
   2 Log[2] Log[3] - (7 Log[3]^2)/3 + 2/3 Log[3] Log[5] - Log[5]^2/3 -
    Log[2] Log[7] - 2/3 Log[3] Log[7] + Log[7]^2/2 - 
   1/3 PolyLog[2, 1/14] + 2/3 PolyLog[2, 1/7] - 
   1/6 PolyLog[2, 16/81] - 2 PolyLog[2, 1/3] - 2/3 PolyLog[2, 2/5] + 
   1/6 PolyLog[2, 36/49] - PolyLog[2, 3 (-1)^(2/3)], 
 PolyLog[2, -2 (-1)^(1/3)] -> -((2 Pi^2)/9) + Log[3]^2/3 - 
   Log[2] Log[7] - 1/3 Log[3] Log[7] + Log[7]^2/3 + 
   1/3 PolyLog[2, 1/7] + 2/3 PolyLog[2, 1/3] + 1/3 PolyLog[2, 3/7] - 
   PolyLog[2, 2 (-1)^(2/3)], 
 PolyLog[2, -(-1)^(1/3)] -> -(Pi^2/18) + (2 I Pi^2)/(
   9 Sqrt[3]) - (I PolyGamma[1, 1/3])/(3 Sqrt[3]), 
 PolyLog[2, -(1/2) (-1)^(1/3)] -> -(Pi^2/9) + 1/3 I Pi Log[2] - 
   Log[2]^2/2 - PolyLog[2, 2 (-1)^(2/3)], 
 PolyLog[2, -(1/3) (-1)^(1/3)] -> -((32 I Catalan)/27) - (89 Pi^2)/
   162 + 8/9 Pi ArcTan[2] + 26/27 Pi ArcTan[5] - 
   32/27 ArcTan[2] ArcTan[5] + 2/9 I Pi Log[2] - 
   8/9 I ArcTan[5] Log[2] - (16 Log[2]^2)/27 + 1/9 I Pi Log[3] + 
   8/9 I ArcTan[5] Log[3] + 22/27 Log[2] Log[3] - (3 Log[3]^2)/2 - 
   8/27 I ArcTan[5] Log[5] - 20/27 Log[2] Log[5] + 
   10/27 Log[3] Log[5] + (2 Log[5]^2)/9 + 2/3 Log[2] Log[7] + 
   4/9 Log[3] Log[7] - Log[7]^2/3 + 8/27 PolyLog[2, -1 + (2 I)/3] + 
   8/9 PolyLog[2, (2 I)/3] + 8/27 PolyLog[2, 5 I] - 
   4/27 PolyLog[2, 1/40] - 2/27 PolyLog[2, 1/26] + 
   2/9 PolyLog[2, 1/14] + 2/27 PolyLog[2, 1/13] - 
   4/9 PolyLog[2, 1/7] - 1/54 PolyLog[2, 16/81] + 
   2/9 PolyLog[2, 1/5] - 34/27 PolyLog[2, 1/3] - 
   16/27 PolyLog[2, 1/3 - I] - 16/27 PolyLog[2, 1/3 + I] + 
   10/27 PolyLog[2, 2/5] - 16/27 PolyLog[2, 2/3 - I] - 
   8/27 PolyLog[2, 2/3 + I] - 1/9 PolyLog[2, 36/49] + 
   10/27 PolyLog[2, 1 - (2 I)/3] + 2/27 PolyLog[2, 1 + (2 I)/3] - 
   PolyLog[2, 3 (-1)^(2/3)], 
 PolyLog[2, -(1/4) (-1)^(1/3)] -> -((32 I Catalan)/81) + (91 Pi^2)/
   486 + (5 I Pi^2)/(9 Sqrt[3]) + 8/27 Pi ArcTan[2] + 
   26/81 Pi ArcTan[5] - 32/81 ArcTan[2] ArcTan[5] - 
   7/27 I Pi Log[2] - 8/27 I ArcTan[5] Log[2] - (178 Log[2]^2)/
   81 - 2/27 I Pi Log[3] + 8/27 I ArcTan[5] Log[3] + 
   103/81 Log[2] Log[3] - (3 Log[3]^2)/2 - 8/81 I ArcTan[5] Log[5] - 
   20/81 Log[2] Log[5] + 10/81 Log[3] Log[5] + (2 Log[5]^2)/27 + 
   20/9 Log[2] Log[7] + 22/27 Log[3] Log[7] - (7 Log[7]^2)/9 - (
   5 I PolyGamma[1, 1/3])/(6 Sqrt[3]) + 
   8/81 PolyLog[2, -1 + (2 I)/3] + 8/27 PolyLog[2, (2 I)/3] + 
   8/81 PolyLog[2, 5 I] - 4/81 PolyLog[2, 1/40] - 
   2/81 PolyLog[2, 1/26] + 2/27 PolyLog[2, 1/14] + 
   2/81 PolyLog[2, 1/13] - 22/27 PolyLog[2, 1/7] - 
   1/162 PolyLog[2, 16/81] + 2/27 PolyLog[2, 1/5] - 
   223/81 PolyLog[2, 1/3] - 16/81 PolyLog[2, 1/3 - I] - 
   16/81 PolyLog[2, 1/3 + I] + 10/81 PolyLog[2, 2/5] - 
   2/3 PolyLog[2, 3/7] - 16/81 PolyLog[2, 2/3 - I] - 
   8/81 PolyLog[2, 2/3 + I] - 1/27 PolyLog[2, 36/49] + 
   10/81 PolyLog[2, 1 - (2 I)/3] + 2/81 PolyLog[2, 1 + (2 I)/3] + 
   2 PolyLog[2, 2 (-1)^(2/3)], 
 PolyLog[2, 1/3 (-1)^(1/3)] -> -(Pi^2/18) - 2/3 I Pi Log[3] - 
   Log[3]^2/6 + 2/3 Log[3] Log[7] - Log[7]^2/6 - 
   2/3 PolyLog[2, 1/7] + 2/3 PolyLog[2, 1/3] + 1/3 PolyLog[2, 3/7] + 
   PolyLog[2, 3 (-1)^(1/3)], 
 PolyLog[2, 1/2 (-1)^(1/3)] -> (16 I Catalan)/81 + (125 Pi^2)/
   972 - (5 I Pi^2)/(18 Sqrt[3]) - 4/27 Pi ArcTan[2] - 
   13/81 Pi ArcTan[5] + 16/81 ArcTan[2] ArcTan[5] - 
   11/54 I Pi Log[2] + 4/27 I ArcTan[5] Log[2] - (65 Log[2]^2)/
   162 + 1/27 I Pi Log[3] - 4/27 I ArcTan[5] Log[3] + 
   59/162 Log[2] Log[3] - Log[3]^2/12 + 4/81 I ArcTan[5] Log[5] + 
   10/81 Log[2] Log[5] - 5/81 Log[3] Log[5] - Log[5]^2/27 - 
   1/9 Log[2] Log[7] - 2/27 Log[3] Log[7] + Log[7]^2/18 + (
   5 I PolyGamma[1, 1/3])/(12 Sqrt[3]) - 
   4/81 PolyLog[2, -1 + (2 I)/3] - 4/27 PolyLog[2, (2 I)/3] - 
   4/81 PolyLog[2, 5 I] + 2/81 PolyLog[2, 1/40] + 
   1/81 PolyLog[2, 1/26] - 1/27 PolyLog[2, 1/14] - 
   1/81 PolyLog[2, 1/13] + 2/27 PolyLog[2, 1/7] + 
   1/324 PolyLog[2, 16/81] - 1/27 PolyLog[2, 1/5] - 
   47/162 PolyLog[2, 1/3] + 8/81 PolyLog[2, 1/3 - I] + 
   8/81 PolyLog[2, 1/3 + I] - 5/81 PolyLog[2, 2/5] + 
   8/81 PolyLog[2, 2/3 - I] + 4/81 PolyLog[2, 2/3 + I] + 
   1/54 PolyLog[2, 36/49] - 5/81 PolyLog[2, 1 - (2 I)/3] - 
   1/81 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, (-1)^(1/3)] -> Pi^2/36 - (I Pi^2)/(3 Sqrt[3]) + (
   I PolyGamma[1, 1/3])/(2 Sqrt[3]), 
 PolyLog[2, 2 (-1)^(1/3)] -> (16 I Catalan)/81 + (71 Pi^2)/972 - (
   5 I Pi^2)/(18 Sqrt[3]) - 4/27 Pi ArcTan[2] - 
   13/81 Pi ArcTan[5] + 16/81 ArcTan[2] ArcTan[5] + 
   25/54 I Pi Log[2] + 4/27 I ArcTan[5] Log[2] + (8 Log[2]^2)/81 + 
   1/27 I Pi Log[3] - 4/27 I ArcTan[5] Log[3] - 
   103/162 Log[2] Log[3] + (5 Log[3]^2)/12 + 
   4/81 I ArcTan[5] Log[5] + 10/81 Log[2] Log[5] - 
   5/81 Log[3] Log[5] - Log[5]^2/27 - 1/9 Log[2] Log[7] - 
   2/27 Log[3] Log[7] + Log[7]^2/18 + (5 I PolyGamma[1, 1/3])/(
   12 Sqrt[3]) - 4/81 PolyLog[2, -1 + (2 I)/3] - 
   4/27 PolyLog[2, (2 I)/3] - 4/81 PolyLog[2, 5 I] + 
   2/81 PolyLog[2, 1/40] + 1/81 PolyLog[2, 1/26] - 
   1/27 PolyLog[2, 1/14] - 1/81 PolyLog[2, 1/13] + 
   2/27 PolyLog[2, 1/7] + 1/324 PolyLog[2, 16/81] - 
   1/27 PolyLog[2, 1/5] + 115/162 PolyLog[2, 1/3] + 
   8/81 PolyLog[2, 1/3 - I] + 8/81 PolyLog[2, 1/3 + I] - 
   5/81 PolyLog[2, 2/5] + 8/81 PolyLog[2, 2/3 - I] + 
   4/81 PolyLog[2, 2/3 + I] + 1/54 PolyLog[2, 36/49] - 
   5/81 PolyLog[2, 1 - (2 I)/3] - 1/81 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, -3 (-1)^(2/3)] -> Pi^2/9 - Log[3]^2/3 - 
   2/3 Log[3] Log[7] + Log[7]^2/6 + 2/3 PolyLog[2, 1/7] - 
   2/3 PolyLog[2, 1/3] - 1/3 PolyLog[2, 3/7] - 
   PolyLog[2, 3 (-1)^(1/3)], 
 PolyLog[2, -2 (-1)^(2/3)] -> -((16 I Catalan)/81) - (71 Pi^2)/
   972 + (5 I Pi^2)/(18 Sqrt[3]) + 4/27 Pi ArcTan[2] + 
   13/81 Pi ArcTan[5] - 16/81 ArcTan[2] ArcTan[5] - 
   25/54 I Pi Log[2] - 4/27 I ArcTan[5] Log[2] - (8 Log[2]^2)/81 - 
   1/27 I Pi Log[3] + 4/27 I ArcTan[5] Log[3] - 
   59/162 Log[2] Log[3] + Log[3]^2/12 - 4/81 I ArcTan[5] Log[5] - 
   10/81 Log[2] Log[5] + 5/81 Log[3] Log[5] + Log[5]^2/27 + 
   1/9 Log[2] Log[7] + 2/27 Log[3] Log[7] - Log[7]^2/18 - (
   5 I PolyGamma[1, 1/3])/(12 Sqrt[3]) + 
   4/81 PolyLog[2, -1 + (2 I)/3] + 4/27 PolyLog[2, (2 I)/3] + 
   4/81 PolyLog[2, 5 I] - 2/81 PolyLog[2, 1/40] - 
   1/81 PolyLog[2, 1/26] + 1/27 PolyLog[2, 1/14] + 
   1/81 PolyLog[2, 1/13] - 2/27 PolyLog[2, 1/7] - 
   1/324 PolyLog[2, 16/81] + 1/27 PolyLog[2, 1/5] + 
   47/162 PolyLog[2, 1/3] - 8/81 PolyLog[2, 1/3 - I] - 
   8/81 PolyLog[2, 1/3 + I] + 5/81 PolyLog[2, 2/5] - 
   8/81 PolyLog[2, 2/3 - I] - 4/81 PolyLog[2, 2/3 + I] - 
   1/54 PolyLog[2, 36/49] + 5/81 PolyLog[2, 1 - (2 I)/3] + 
   1/81 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, -(-1)^(2/3)] -> Pi^2/36 + (I Pi^2)/(3 Sqrt[3]) - (
   I PolyGamma[1, 1/3])/(2 Sqrt[3]), 
 PolyLog[2, -(1/2) (-1)^(2/3)] -> -((16 I Catalan)/81) - (17 Pi^2)/
   972 + (5 I Pi^2)/(18 Sqrt[3]) + 4/27 Pi ArcTan[2] + 
   13/81 Pi ArcTan[5] - 16/81 ArcTan[2] ArcTan[5] + 
   11/54 I Pi Log[2] - 4/27 I ArcTan[5] Log[2] - (97 Log[2]^2)/
   162 - 1/27 I Pi Log[3] + 4/27 I ArcTan[5] Log[3] + 
   103/162 Log[2] Log[3] - (5 Log[3]^2)/12 - 
   4/81 I ArcTan[5] Log[5] - 10/81 Log[2] Log[5] + 
   5/81 Log[3] Log[5] + Log[5]^2/27 + 1/9 Log[2] Log[7] + 
   2/27 Log[3] Log[7] - Log[7]^2/18 - (5 I PolyGamma[1, 1/3])/(
   12 Sqrt[3]) + 4/81 PolyLog[2, -1 + (2 I)/3] + 
   4/27 PolyLog[2, (2 I)/3] + 4/81 PolyLog[2, 5 I] - 
   2/81 PolyLog[2, 1/40] - 1/81 PolyLog[2, 1/26] + 
   1/27 PolyLog[2, 1/14] + 1/81 PolyLog[2, 1/13] - 
   2/27 PolyLog[2, 1/7] - 1/324 PolyLog[2, 16/81] + 
   1/27 PolyLog[2, 1/5] - 115/162 PolyLog[2, 1/3] - 
   8/81 PolyLog[2, 1/3 - I] - 8/81 PolyLog[2, 1/3 + I] + 
   5/81 PolyLog[2, 2/5] - 8/81 PolyLog[2, 2/3 - I] - 
   4/81 PolyLog[2, 2/3 + I] - 1/54 PolyLog[2, 36/49] + 
   5/81 PolyLog[2, 1 - (2 I)/3] + 1/81 PolyLog[2, 1 + (2 I)/3], 
 PolyLog[2, -(1/3) (-1)^(2/3)] -> Pi^2/18 + 2/3 I Pi Log[3] - 
   Log[3]^2/2 - PolyLog[2, 3 (-1)^(1/3)], 
 PolyLog[2, -(1/4) (-1)^(2/3)] -> -((64 I Catalan)/27) - (97 Pi^2)/
   162 + 16/9 Pi ArcTan[2] + 52/27 Pi ArcTan[5] - 
   64/27 ArcTan[2] ArcTan[5] + 4/9 I Pi Log[2] - 
   16/9 I ArcTan[5] Log[2] - (131 Log[2]^2)/27 - 4/9 I Pi Log[3] + 
   16/9 I ArcTan[5] Log[3] + 98/27 Log[2] Log[3] - (13 Log[3]^2)/3 - 
   16/27 I ArcTan[5] Log[5] - 40/27 Log[2] Log[5] + 
   38/27 Log[3] Log[5] + Log[5]^2/9 + 10/3 Log[2] Log[7] + 
   20/9 Log[3] Log[7] - (5 Log[7]^2)/3 + 
   16/27 PolyLog[2, -1 + (2 I)/3] + 16/9 PolyLog[2, (2 I)/3] + 
   16/27 PolyLog[2, 5 I] - 8/27 PolyLog[2, 1/40] - 
   4/27 PolyLog[2, 1/26] + 10/9 PolyLog[2, 1/14] + 
   4/27 PolyLog[2, 1/13] - 20/9 PolyLog[2, 1/7] - 
   11/54 PolyLog[2, 16/81] + 4/9 PolyLog[2, 1/5] - 
   122/27 PolyLog[2, 1/3] - 32/27 PolyLog[2, 1/3 - I] - 
   32/27 PolyLog[2, 1/3 + I] + 2/27 PolyLog[2, 2/5] - 
   32/27 PolyLog[2, 2/3 - I] - 16/27 PolyLog[2, 2/3 + I] - 
   5/9 PolyLog[2, 36/49] + 20/27 PolyLog[2, 1 - (2 I)/3] + 
   4/27 PolyLog[2, 1 + (2 I)/3] - PolyLog[2, 1/4 (-1)^(1/3)], 
 PolyLog[2, 1/4 (-1)^(2/3)] -> (32 I Catalan)/81 + (17 Pi^2)/
   486 - (5 I Pi^2)/(9 Sqrt[3]) - 8/27 Pi ArcTan[2] - 
   26/81 Pi ArcTan[5] + 32/81 ArcTan[2] ArcTan[5] + 
   7/27 I Pi Log[2] + 8/27 I ArcTan[5] Log[2] - (146 Log[2]^2)/
   81 + 2/27 I Pi Log[3] - 8/27 I ArcTan[5] Log[3] + 
   59/81 Log[2] Log[3] - Log[3]^2/6 + 8/81 I ArcTan[5] Log[5] + 
   20/81 Log[2] Log[5] - 10/81 Log[3] Log[5] - (2 Log[5]^2)/27 - 
   2/9 Log[2] Log[7] - 4/27 Log[3] Log[7] + Log[7]^2/9 + (
   5 I PolyGamma[1, 1/3])/(6 Sqrt[3]) - 
   8/81 PolyLog[2, -1 + (2 I)/3] - 8/27 PolyLog[2, (2 I)/3] - 
   8/81 PolyLog[2, 5 I] + 4/81 PolyLog[2, 1/40] + 
   2/81 PolyLog[2, 1/26] - 2/27 PolyLog[2, 1/14] - 
   2/81 PolyLog[2, 1/13] + 4/27 PolyLog[2, 1/7] + 
   1/162 PolyLog[2, 16/81] - 2/27 PolyLog[2, 1/5] - 
   47/81 PolyLog[2, 1/3] + 16/81 PolyLog[2, 1/3 - I] + 
   16/81 PolyLog[2, 1/3 + I] - 10/81 PolyLog[2, 2/5] + 
   16/81 PolyLog[2, 2/3 - I] + 8/81 PolyLog[2, 2/3 + I] + 
   1/27 PolyLog[2, 36/49] - 10/81 PolyLog[2, 1 - (2 I)/3] - 
   2/81 PolyLog[2, 1 + (2 I)/3] - 2 PolyLog[2, 2 (-1)^(2/3)], 
 PolyLog[2, 1/3 (-1)^(2/3)] -> -(Pi^2/12) + Log[2]^2/6 - 
   1/3 I Pi Log[3] - 2 Log[2] Log[3] + (11 Log[3]^2)/6 - 
   2/3 Log[3] Log[5] + Log[5]^2/3 + Log[2] Log[7] + 
   2/3 Log[3] Log[7] - Log[7]^2/2 + 1/3 PolyLog[2, 1/14] - 
   2/3 PolyLog[2, 1/7] + 1/6 PolyLog[2, 16/81] + 2 PolyLog[2, 1/3] + 
   2/3 PolyLog[2, 2/5] - 1/6 PolyLog[2, 36/49] + 
   PolyLog[2, 3 (-1)^(2/3)], 
 PolyLog[2, 1/2 (-1)^(2/3)] -> Pi^2/9 - 1/3 I Pi Log[2] - 
   Log[2]^2/2 - Log[3]^2/3 + Log[2] Log[7] + 1/3 Log[3] Log[7] - 
   Log[7]^2/3 - 1/3 PolyLog[2, 1/7] - 2/3 PolyLog[2, 1/3] - 
   1/3 PolyLog[2, 3/7] + PolyLog[2, 2 (-1)^(2/3)], 
 PolyLog[2, (-1)^(2/3)] -> -(Pi^2/18) - (2 I Pi^2)/(
   9 Sqrt[3]) + (I PolyGamma[1, 1/3])/(3 Sqrt[3]), 
 PolyLog[2, -(1/2) (-1)^(3/4)] -> -(Pi^2/48) + 1/2 I Pi Log[2] -
    Log[2]^2 - 1/2 PolyLog[2, 4 I] - PolyLog[2, 1/2 (-1)^(3/4)], 
 PolyLog[2, -(1/3) (-1)^(3/4)] -> -(Pi^2/48) + 1/2 I Pi Log[3] -
    Log[3]^2 - 1/2 PolyLog[2, 9 I] - PolyLog[2, 1/3 (-1)^(3/4)], 
 PolyLog[2, (-1)^(3/4)] -> -((I Catalan)/4) - (I Catalan)/Sqrt[
   2] - (13/192 + I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, -((1 + I)/Sqrt[2])] -> (I Catalan)/4 + (I Catalan)/Sqrt[
   2] - (13/192 - I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) - (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, -(I/Sqrt[2])] -> 
  2/3 I Sqrt[2] Catalan + (5/72 + I/12) Pi^2 + (I Pi^2)/(
   6 Sqrt[2]) - 5/24 Pi ArcTan[Sqrt[2]] + 3/8 I Pi Log[2] - 
   1/4 I ArcTan[Sqrt[2]] Log[2] - Log[2]^2/8 - 5/48 I Pi Log[3] + 
   1/8 Log[2] Log[3] + 1/12 I Pi Log[1 + Sqrt[2]] + 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   1/12 Log[3] Log[1 + Sqrt[2]] - (I PolyGamma[1, 1/8])/(
   12 Sqrt[2]) + 1/3 PolyLog[2, I + Sqrt[2]] - 
   1/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, I/Sqrt[
   2]] -> -(2/3) I Sqrt[2] Catalan - (5/72 + I/12) Pi^2 - (
   I Pi^2)/(6 Sqrt[2]) + 5/24 Pi ArcTan[Sqrt[2]] - 
   3/8 I Pi Log[2] + 1/4 I ArcTan[Sqrt[2]] Log[2] - Log[2]^2/8 + 
   5/48 I Pi Log[3] + 3/8 Log[2] Log[3] - Log[3]^2/4 - 
   1/12 I Pi Log[1 + Sqrt[2]] - 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 
   1/12 Log[3] Log[1 + Sqrt[2]] + (I PolyGamma[1, 1/8])/(
   12 Sqrt[2]) - 1/2 PolyLog[2, 1/3] - 1/3 PolyLog[2, I + Sqrt[2]] + 
   1/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, (1 + I)/Sqrt[2]] -> (I Catalan)/4 - (I Catalan)/Sqrt[
   2] + (11/192 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, -I Sqrt[2]] -> 
  2/3 I Sqrt[2] Catalan + (1/36 + I/12) Pi^2 + (I Pi^2)/(
   6 Sqrt[2]) - 5/24 Pi ArcTan[Sqrt[2]] + 1/8 I Pi Log[2] - 
   1/4 I ArcTan[Sqrt[2]] Log[2] - 5/48 I Pi Log[3] - 
   3/8 Log[2] Log[3] + Log[3]^2/4 + 1/12 I Pi Log[1 + Sqrt[2]] + 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   1/12 Log[3] Log[1 + Sqrt[2]] - (I PolyGamma[1, 1/8])/(
   12 Sqrt[2]) + 1/2 PolyLog[2, 1/3] + 1/3 PolyLog[2, I + Sqrt[2]] - 
   1/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 
   I Sqrt[2]] -> -(2/3) I Sqrt[2] Catalan - (1/9 + I/12) Pi^2 - (
   I Pi^2)/(6 Sqrt[2]) + 5/24 Pi ArcTan[Sqrt[2]] - 
   1/8 I Pi Log[2] + 1/4 I ArcTan[Sqrt[2]] Log[2] + 
   5/48 I Pi Log[3] - 1/8 Log[2] Log[3] - 
   1/12 I Pi Log[1 + Sqrt[2]] - 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 
   1/12 Log[3] Log[1 + Sqrt[2]] + (I PolyGamma[1, 1/8])/(
   12 Sqrt[2]) - 1/3 PolyLog[2, I + Sqrt[2]] + 
   1/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, -2 I Sqrt[2]] -> -((13 Pi^2)/24) + 
   5/4 Pi ArcTan[Sqrt[2]] - 9/4 I Pi Log[2] + 
   3/2 I ArcTan[Sqrt[2]] Log[2] + 5/8 I Pi Log[3] - 
   3/4 Log[2] Log[3] - 1/2 I Pi Log[1 + Sqrt[2]] - 
   I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 1/2 Log[3] Log[1 + Sqrt[2]] - 
   2 PolyLog[2, I + Sqrt[2]] + 2 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 2 I Sqrt[2]] -> (7 Pi^2)/24 - 
   5/4 Pi ArcTan[Sqrt[2]] + 9/4 I Pi Log[2] - 
   3/2 I ArcTan[Sqrt[2]] Log[2] - 5/8 I Pi Log[3] - 
   9/4 Log[2] Log[3] + (3 Log[3]^2)/2 + 1/2 I Pi Log[1 + Sqrt[2]] +
    I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   1/2 Log[3] Log[1 + Sqrt[2]] + 3 PolyLog[2, 1/3] + 
   2 PolyLog[2, I + Sqrt[2]] - 2 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, -(1/Sqrt[3])] -> 
  1/2 PolyLog[2, 1/3] - PolyLog[2, 1/Sqrt[3]], 
 PolyLog[2, -(I/Sqrt[3])] -> -(Pi^2/24) + (5 I Pi^2)/(
   18 Sqrt[3]) + 1/12 I Pi Log[3] + Log[3]^2/8 - (
   5 I PolyGamma[1, 1/3])/(12 Sqrt[3]) + 1/2 PolyLog[2, 1/3], 
 PolyLog[2, I/Sqrt[3]] -> -(Pi^2/24) - (5 I Pi^2)/(
   18 Sqrt[3]) - 1/12 I Pi Log[3] + Log[3]^2/8 + (
   5 I PolyGamma[1, 1/3])/(12 Sqrt[3]) + 1/2 PolyLog[2, 1/3], 
 PolyLog[2, -Sqrt[3]] -> -(Pi^2/6) - Log[3]^2/8 - 
   1/2 PolyLog[2, 1/3] + PolyLog[2, 1/Sqrt[3]], 
 PolyLog[2, -I Sqrt[3]] -> (5 I Pi^2)/(18 Sqrt[3]) - 
   1/6 I Pi Log[3] - Log[3]^2/4 - (5 I PolyGamma[1, 1/3])/(
   12 Sqrt[3]) - 1/2 PolyLog[2, 1/3], 
 PolyLog[2, I Sqrt[3]] -> -((5 I Pi^2)/(18 Sqrt[3])) + 
   1/6 I Pi Log[3] - Log[3]^2/4 + (5 I PolyGamma[1, 1/3])/(
   12 Sqrt[3]) - 1/2 PolyLog[2, 1/3], 
 PolyLog[2, Sqrt[3]] -> Pi^2/3 - 1/2 I Pi Log[3] - Log[3]^2/8 - 
   PolyLog[2, 1/Sqrt[3]], 
 PolyLog[2, -I Sqrt[5]] -> -(Pi^2/24) - 1/2 Log[2] Log[3] + 
   Log[3]^2/4 + 1/2 Log[2] Log[5] - Log[5]^2/2 - 
   1/2 PolyLog[2, 1/5] + 1/2 PolyLog[2, 1/3] - 1/2 PolyLog[2, 2/5] - 
   PolyLog[2, I Sqrt[5]], 
 PolyLog[2, 1 - (-1)^(1/8)] -> -((3 I Catalan)/56) + (3 I Catalan)/(
   14 Sqrt[2]) - 
   4/7 I Sqrt[2 + Sqrt[2]] Catalan - (3/128 - (3 I)/224) Pi^2 + (
   17 I Pi^2)/(80 Sqrt[2]) - 2/35 I Sqrt[2] Pi^2 - 
   1/28 I Sqrt[2 - Sqrt[2]] Pi^2 - 
   1/28 I Sqrt[2 + Sqrt[2]] Pi^2 - 1/32 I Pi Log[2] + 
   1/16 I Pi Log[1 + Sqrt[2]] - 
   1/112 I Sqrt[2 - Sqrt[2]] PolyGamma[1, 1/16] - (
   3 I PolyGamma[1, 1/8])/(224 Sqrt[2]) + 
   1/56 I Sqrt[2 - Sqrt[2]] PolyGamma[1, 1/8] + 
   1/56 I Sqrt[2 + Sqrt[2]] PolyGamma[1, 1/8] - 
   1/112 I Sqrt[2 + Sqrt[2]] PolyGamma[1, 3/16] + 
   1/7 PolyLog[2, 1 + (-1)^(1/8)], 
 PolyLog[2, 1/2 (1 - (-1)^(1/4))] -> (I Catalan)/Sqrt[
   2] + (71/384 + I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) + 
   3/32 I Pi Log[2] - (15 Log[2]^2)/32 + 
   1/16 I Pi Log[1 + Sqrt[2]] - 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 - (I PolyGamma[1, 1/8])/(16 Sqrt[2]) - 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1 - (-1)^(1/4)] -> -((I Catalan)/4) + (I Catalan)/Sqrt[
   2] + (1/64 + I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) - 
   1/16 I Pi Log[2] + 1/8 I Pi Log[1 + Sqrt[2]] - (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, 
   1/2 (1 + (-1)^(1/4))] -> -((I Catalan)/Sqrt[
    2]) - (25/384 + I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) - 
   9/32 I Pi Log[2] - (3 Log[2]^2)/32 + 
   3/16 I Pi Log[1 + Sqrt[2]] + 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 + (I PolyGamma[1, 1/8])/(16 Sqrt[2]) + 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1 + (-1)^(1/4)] -> -((I Catalan)/4) - (I Catalan)/Sqrt[
   2] + (9/64 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) + 
   3/16 I Pi Log[2] + 3/8 I Pi Log[1 + Sqrt[2]] + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, 1 - (-1)^(1/3)] -> Pi^2/36 + (I Pi^2)/(
   3 Sqrt[3]) - (I PolyGamma[1, 1/3])/(2 Sqrt[3]), 
 PolyLog[2, 1 + (-1)^(1/3)] -> Pi^2/9 - (2 I Pi^2)/(
   9 Sqrt[3]) + 1/3 I Pi Log[3] + (I PolyGamma[1, 1/3])/(
   3 Sqrt[3]), 
 PolyLog[2, 1 - (-1)^(3/8)] -> (9 Pi^2)/128 - 
   PolyLog[2, 1 + (-1)^(5/8)], 
 PolyLog[2, 1 - (-1)^(5/8)] -> (I Catalan)/24 + (I Catalan)/(
   6 Sqrt[2]) + 
   4/3 I Sqrt[2 - Sqrt[2]] Catalan + (5/128 + I/96) Pi^2 + (
   53 I Pi^2)/(240 Sqrt[2]) + 1/15 I Sqrt[2] Pi^2 - 
   1/12 I Sqrt[2 - Sqrt[2]] Pi^2 + 
   1/12 I Sqrt[2 + Sqrt[2]] Pi^2 - 5/32 I Pi Log[2] - 
   5/16 I Pi Log[1 + Sqrt[2]] - 
   1/48 I Sqrt[2 + Sqrt[2]] PolyGamma[1, 1/16] - (
   I PolyGamma[1, 1/8])/(96 Sqrt[2]) - 
   1/24 I Sqrt[2 - Sqrt[2]] PolyGamma[1, 1/8] + 
   1/24 I Sqrt[2 + Sqrt[2]] PolyGamma[1, 1/8] + 
   1/48 I Sqrt[2 - Sqrt[2]] PolyGamma[1, 3/16] + 
   5/3 PolyLog[2, 1 + (-1)^(5/8)], 
 PolyLog[2, 1 - (-1)^(2/3)] -> Pi^2/9 + (2 I Pi^2)/(
   9 Sqrt[3]) - 1/3 I Pi Log[3] - (I PolyGamma[1, 1/3])/(
   3 Sqrt[3]), 
 PolyLog[2, 1 + (-1)^(2/3)] -> Pi^2/36 - (I Pi^2)/(
   3 Sqrt[3]) + (I PolyGamma[1, 1/3])/(2 Sqrt[3]), 
 PolyLog[2, 1/2 (1 - (-1)^(3/4))] -> (I Catalan)/Sqrt[
   2] - (25/384 - I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) + 
   9/32 I Pi Log[2] - (3 Log[2]^2)/32 - 
   3/16 I Pi Log[1 + Sqrt[2]] + 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 - (I PolyGamma[1, 1/8])/(16 Sqrt[2]) + 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1 - (-1)^(3/4)] -> (I Catalan)/4 + (I Catalan)/Sqrt[
   2] + (9/64 + I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) - 
   3/16 I Pi Log[2] - 3/8 I Pi Log[1 + Sqrt[2]] - (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, 
   1/2 (1 + (-1)^(3/4))] -> -((I Catalan)/Sqrt[
    2]) + (71/384 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) - 
   3/32 I Pi Log[2] - (15 Log[2]^2)/32 - 
   1/16 I Pi Log[1 + Sqrt[2]] - 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 + (I PolyGamma[1, 1/8])/(16 Sqrt[2]) - 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1 + (-1)^(3/4)] -> (I Catalan)/4 - (I Catalan)/Sqrt[
   2] + (1/64 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) + 
   1/16 I Pi Log[2] - 1/8 I Pi Log[1 + Sqrt[2]] + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]), 
 PolyLog[2, 1 - (-1)^(7/8)] -> (49 Pi^2)/128 - 
   PolyLog[2, 1 + (-1)^(1/8)], 
 PolyLog[2, 1 + (-1)^(7/8)] -> (3 I Catalan)/56 - (3 I Catalan)/(
   14 Sqrt[2]) + 
   4/7 I Sqrt[2 + Sqrt[2]] Catalan + (1/32 - (3 I)/224) Pi^2 - (
   17 I Pi^2)/(80 Sqrt[2]) + 2/35 I Sqrt[2] Pi^2 + 
   1/28 I Sqrt[2 - Sqrt[2]] Pi^2 + 
   1/28 I Sqrt[2 + Sqrt[2]] Pi^2 + 1/32 I Pi Log[2] - 
   1/16 I Pi Log[1 + Sqrt[2]] + 
   1/112 I Sqrt[2 - Sqrt[2]] PolyGamma[1, 1/16] + (
   3 I PolyGamma[1, 1/8])/(224 Sqrt[2]) - 
   1/56 I Sqrt[2 - Sqrt[2]] PolyGamma[1, 1/8] - 
   1/56 I Sqrt[2 + Sqrt[2]] PolyGamma[1, 1/8] + 
   1/112 I Sqrt[2 + Sqrt[2]] PolyGamma[1, 3/16] - 
   1/7 PolyLog[2, 1 + (-1)^(1/8)], 
 PolyLog[2, -I - Sqrt[2]] -> (5 Pi^2)/48 - 
   1/8 Pi ArcTan[Sqrt[2]] + 3/8 I Pi Log[2] + 
   3/4 I ArcTan[Sqrt[2]] Log[2] - 1/16 I Pi Log[3] - 
   3/8 Log[2] Log[3] + 1/4 I Pi Log[1 + Sqrt[2]] + 
   1/2 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   1/4 Log[3] Log[1 + Sqrt[2]] - PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, I - Sqrt[2]] -> -((5 Pi^2)/16) + 
   9/8 Pi ArcTan[Sqrt[2]] - 3/8 I Pi Log[2] - 
   3/4 I ArcTan[Sqrt[2]] Log[2] + 1/16 I Pi Log[3] + 
   3/8 Log[2] Log[3] - (3 Log[3]^2)/4 - 
   1/4 I Pi Log[1 + Sqrt[2]] - 
   1/2 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 
   1/4 Log[3] Log[1 + Sqrt[2]] - 3/2 PolyLog[2, 1/3] - 
   PolyLog[2, -I + Sqrt[2]] - PolyLog[2, I + Sqrt[2]] + 
   PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, I (1 - Sqrt[2])] -> (I Catalan)/Sqrt[
   2] - (17/96 - I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) + (
   3 Log[2]^2)/16 + 1/8 I Pi Log[1 + Sqrt[2]] + 
   3/4 Log[2] Log[1 + Sqrt[2]] - 1/4 Log[1 + Sqrt[2]]^2 - (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]) + 3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, (1 - I) - Sqrt[2]] -> -((7 Pi^2)/48) + 
   5/8 Pi ArcTan[Sqrt[2]] - 3/8 I Pi Log[2] + 
   3/4 I ArcTan[Sqrt[2]] Log[2] + 5/16 I Pi Log[3] - 
   3/8 Log[2] Log[3] + 1/4 I Pi Log[1 + Sqrt[2]] - 
   1/2 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 
   1/4 Log[3] Log[1 + Sqrt[2]] - PolyLog[2, I + Sqrt[2]], 
 PolyLog[2, (1 + I) - Sqrt[2]] -> -((7 Pi^2)/48) + 
   5/8 Pi ArcTan[Sqrt[2]] + 3/8 I Pi Log[2] - 
   3/4 I ArcTan[Sqrt[2]] Log[2] - 5/16 I Pi Log[3] - 
   3/8 Log[2] Log[3] - 1/4 I Pi Log[1 + Sqrt[2]] + 
   1/2 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 
   1/4 Log[3] Log[1 + Sqrt[2]] - PolyLog[2, -I + Sqrt[2]], 
 PolyLog[2, 1/4 (2 - Sqrt[2])] -> (17 Pi^2)/24 - (15 Log[2]^2)/8 - 
   3/2 Log[2] Log[1 + Sqrt[2]] + 1/2 Log[1 + Sqrt[2]]^2 - 
   6 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 2 - Sqrt[2]] -> (5 Pi^2)/24 - Log[2]^2/8 - 
   1/2 Log[1 + Sqrt[2]]^2 - PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1 - I Sqrt[2]] -> 
  2/3 I Sqrt[2] Catalan + (5/18 + I/12) Pi^2 + (I Pi^2)/(
   6 Sqrt[2]) - 17/24 Pi ArcTan[Sqrt[2]] + 1/8 I Pi Log[2] + 
   1/4 I ArcTan[Sqrt[2]] Log[2] - 17/48 I Pi Log[3] - 
   1/8 Log[2] Log[3] + 1/12 I Pi Log[1 + Sqrt[2]] + 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   1/12 Log[3] Log[1 + Sqrt[2]] - (I PolyGamma[1, 1/8])/(
   12 Sqrt[2]) + 1/3 PolyLog[2, I + Sqrt[2]] - 
   1/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 
   1 + I Sqrt[2]] -> -(2/3) I Sqrt[2]
     Catalan + (5/36 - I/12) Pi^2 - (I Pi^2)/(6 Sqrt[2]) - 
   7/24 Pi ArcTan[Sqrt[2]] - 1/8 I Pi Log[2] - 
   1/4 I ArcTan[Sqrt[2]] Log[2] + 17/48 I Pi Log[3] + 
   1/8 Log[2] Log[3] - Log[3]^2/4 - 1/12 I Pi Log[1 + Sqrt[2]] - 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] + 
   1/12 Log[3] Log[1 + Sqrt[2]] + (I PolyGamma[1, 1/8])/(
   12 Sqrt[2]) - 1/2 PolyLog[2, 1/3] - 1/3 PolyLog[2, I + Sqrt[2]] + 
   1/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 
   I (-1 + Sqrt[2])] -> -((I Catalan)/Sqrt[
    2]) - (17/96 + I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) + (
   3 Log[2]^2)/16 - 1/8 I Pi Log[1 + Sqrt[2]] + 
   3/4 Log[2] Log[1 + Sqrt[2]] - 1/4 Log[1 + Sqrt[2]]^2 + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]) + 3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1/((-1 - I) + Sqrt[2])] -> (11 Pi^2)/384 - 
   15/32 I Pi Log[2] - (9 Log[2]^2)/32 + 
   5/16 I Pi Log[1 + Sqrt[2]] + 3/8 Log[2] Log[1 + Sqrt[2]] - 
   1/8 Log[1 + Sqrt[2]]^2 - PolyLog[2, (-1 - I) + Sqrt[2]], 
 PolyLog[2, 2/((-1 - I) + Sqrt[2])] -> (5 I Catalan)/4 - (
   7 I Catalan)/(3 Sqrt[2]) + 
   I Sqrt[2] Catalan + (125/576 - I/48) Pi^2 - (I Pi^2)/(
   24 Sqrt[2]) - 25/24 Pi ArcTan[Sqrt[2]] + 7/16 I Pi Log[2] + 
   1/4 I ArcTan[Sqrt[2]] Log[2] + 5/48 I Pi Log[3] - 
   3/8 Log[2] Log[3] + Log[3]^2/2 + 13/24 I Pi Log[1 + Sqrt[2]] - 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   5/12 Log[3] Log[1 + Sqrt[2]] + (I PolyGamma[1, 1/8])/(48 Sqrt[2]) +
    PolyLog[2, 1/3] + PolyLog[2, -I + Sqrt[2]] + 
   2/3 PolyLog[2, I + Sqrt[2]] - 2/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, (-1 + Sqrt[2])/((-1 - I) + Sqrt[2])] -> -((I Catalan)/
    Sqrt[2]) + (71/384 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) - 
   3/32 I Pi Log[2] - (15 Log[2]^2)/32 - 
   1/16 I Pi Log[1 + Sqrt[2]] - 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 + (I PolyGamma[1, 1/8])/(16 Sqrt[2]) - 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 2/((-1 + I) + Sqrt[2])] -> -((5 I Catalan)/4) + (
   I Catalan)/Sqrt[2] - 
   1/3 I Sqrt[2] Catalan - (35/576 - I/48) Pi^2 + (I Pi^2)/(
   24 Sqrt[2]) - 5/24 Pi ArcTan[Sqrt[2]] - 7/16 I Pi Log[2] - 
   1/4 I ArcTan[Sqrt[2]] Log[2] - 5/48 I Pi Log[3] + 
   1/8 Log[2] Log[3] - 13/24 I Pi Log[1 + Sqrt[2]] + 
   1/6 I ArcTan[Sqrt[2]] Log[1 + Sqrt[2]] - 
   1/12 Log[3] Log[1 + Sqrt[2]] - (I PolyGamma[1, 1/8])/(
   48 Sqrt[2]) + 1/3 PolyLog[2, I + Sqrt[2]] + 
   2/3 PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, (-1 + Sqrt[2])/((-1 + I) + Sqrt[2])] -> (I Catalan)/Sqrt[
   2] + (71/384 + I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) + 
   3/32 I Pi Log[2] - (15 Log[2]^2)/32 + 
   1/16 I Pi Log[1 + Sqrt[2]] - 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 - (I PolyGamma[1, 1/8])/(16 Sqrt[2]) - 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, -I (1 + Sqrt[2])] -> (I Catalan)/Sqrt[
   2] + (13/96 + I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) - (
   3 Log[2]^2)/16 - 3/8 I Pi Log[1 + Sqrt[2]] - 
   3/4 Log[2] Log[1 + Sqrt[2]] - 1/4 Log[1 + Sqrt[2]]^2 - (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]) - 3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 
   I (1 + Sqrt[2])] -> -((I Catalan)/Sqrt[
    2]) + (13/96 - I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) - (
   3 Log[2]^2)/16 + 3/8 I Pi Log[1 + Sqrt[2]] - 
   3/4 Log[2] Log[1 + Sqrt[2]] - 1/4 Log[1 + Sqrt[2]]^2 + (
   I PolyGamma[1, 1/8])/(16 Sqrt[2]) - 3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, 1/((1 - I) + Sqrt[2])] -> -((77 Pi^2)/384) + 
   5/4 Pi ArcTan[Sqrt[2]] - 21/32 I Pi Log[2] - (9 Log[2]^2)/
   32 + 3/4 Log[2] Log[3] - (3 Log[3]^2)/4 - 
   7/16 I Pi Log[1 + Sqrt[2]] - 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/2 Log[3] Log[1 + Sqrt[2]] - 1/8 Log[1 + Sqrt[2]]^2 - 
   3/2 PolyLog[2, 1/3] - PolyLog[2, -I + Sqrt[2]] - 
   PolyLog[2, I + Sqrt[2]] + PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 2/((1 - I) + Sqrt[2])] -> (3 I Catalan)/4 + (29 Pi^2)/
   192 + 1/16 I Pi Log[2] - Log[2]^2/16 - 
   1/8 I Pi Log[1 + Sqrt[2]] - 1/4 Log[1 + Sqrt[2]]^2 - 
   1/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, (
   1 + Sqrt[2])/((1 - I) + Sqrt[2])] -> -((I Catalan)/Sqrt[
    2]) - (25/384 + I/16) Pi^2 - (I Pi^2)/(8 Sqrt[2]) - 
   9/32 I Pi Log[2] - (3 Log[2]^2)/32 + 
   3/16 I Pi Log[1 + Sqrt[2]] + 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 + (I PolyGamma[1, 1/8])/(16 Sqrt[2]) + 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, (1 - I) + Sqrt[2]] -> (5 Pi^2)/12 - 
   5/4 Pi ArcTan[Sqrt[2]] - 3/4 Log[2] Log[3] + (3 Log[3]^2)/4 - 
   1/2 Log[3] Log[1 + Sqrt[2]] + 3/2 PolyLog[2, 1/3] + 
   PolyLog[2, -I + Sqrt[2]] + PolyLog[2, I + Sqrt[2]] - 
   PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 1/((1 + I) + Sqrt[2])] -> (83 Pi^2)/384 + 
   21/32 I Pi Log[2] - (9 Log[2]^2)/32 + 
   7/16 I Pi Log[1 + Sqrt[2]] - 3/8 Log[2] Log[1 + Sqrt[2]] - 
   1/8 Log[1 + Sqrt[2]]^2 - PolyLog[2, (1 + I) + Sqrt[2]], 
 PolyLog[2, 2/((1 + I) + Sqrt[2])] -> -((3 I Catalan)/4) + (
   29 Pi^2)/192 - 1/16 I Pi Log[2] - Log[2]^2/16 + 
   1/8 I Pi Log[1 + Sqrt[2]] - 1/4 Log[1 + Sqrt[2]]^2 - 
   1/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, (1 + Sqrt[2])/((1 + I) + Sqrt[2])] -> (I Catalan)/Sqrt[
   2] - (25/384 - I/16) Pi^2 + (I Pi^2)/(8 Sqrt[2]) + 
   9/32 I Pi Log[2] - (3 Log[2]^2)/32 - 
   3/16 I Pi Log[1 + Sqrt[2]] + 3/8 Log[2] Log[1 + Sqrt[2]] + 
   1/8 Log[1 + Sqrt[2]]^2 - (I PolyGamma[1, 1/8])/(16 Sqrt[2]) + 
   3/2 PolyLog[2, 1/Sqrt[2]], 
 PolyLog[2, -2 - Sqrt[3]] -> -(Pi^2/4) - I Pi Log[2] + 
   1/2 Log[2] Log[3] + 2 I Pi Log[1 + Sqrt[3]] - 
   Log[3] Log[1 + Sqrt[3]] + 1/2 PolyLog[2, 1/3] - 
   2 PolyLog[2, 1/Sqrt[3]] + PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, I (2 - Sqrt[3])] -> (2 I Catalan)/3 + (9 Pi^2)/16 + 
   25/12 I Pi Log[2] - (3 Log[2]^2)/4 - 
   25/6 I Pi Log[1 + Sqrt[3]] + 3 Log[2] Log[1 + Sqrt[3]] - 
   3 Log[1 + Sqrt[3]]^2 - 2 PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, 2 - Sqrt[3]] -> Pi^2/3 + I Pi Log[2] - Log[2]^2/2 - 
   2 I Pi Log[1 + Sqrt[3]] + 2 Log[2] Log[1 + Sqrt[3]] - 
   2 Log[1 + Sqrt[3]]^2 - PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, 3/4 + (I Sqrt[3])/4] -> Pi^2/18 - (5 I Pi^2)/(
   18 Sqrt[3]) - 1/3 I Pi Log[2] - Log[2]^2/2 + 
   1/6 I Pi Log[3] + Log[3]^2/4 + (5 I PolyGamma[1, 1/3])/(
   12 Sqrt[3]) + 1/2 PolyLog[2, 1/3], 
 PolyLog[2, 1/6 (3 - I Sqrt[3])] -> (5 Pi^2)/72 + (2 I Pi^2)/(
   9 Sqrt[3]) + 1/12 I Pi Log[3] - Log[3]^2/8 - (
   I PolyGamma[1, 1/3])/(3 Sqrt[3]), 
 PolyLog[2, 1/6 (3 + I Sqrt[3])] -> (5 Pi^2)/72 - (2 I Pi^2)/(
   9 Sqrt[3]) - 1/12 I Pi Log[3] - Log[3]^2/8 + (
   I PolyGamma[1, 1/3])/(3 Sqrt[3]), 
 PolyLog[2, I (-2 + Sqrt[3])] -> -((2 I Catalan)/3) + (9 Pi^2)/
   16 + 23/12 I Pi Log[2] - (3 Log[2]^2)/4 - 
   23/6 I Pi Log[1 + Sqrt[3]] + 3 Log[2] Log[1 + Sqrt[3]] - 
   3 Log[1 + Sqrt[3]]^2 - 2 PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, -2 + Sqrt[3]] -> Pi^2/12 + I Pi Log[2] - Log[2]^2/
   2 - 1/2 Log[2] Log[3] - 2 I Pi Log[1 + Sqrt[3]] + 
   2 Log[2] Log[1 + Sqrt[3]] + Log[3] Log[1 + Sqrt[3]] - 
   2 Log[1 + Sqrt[3]]^2 - 1/2 PolyLog[2, 1/3] + 
   2 PolyLog[2, 1/Sqrt[3]] - PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, 1/2 (-1 + Sqrt[3])] -> -(1/8) Log[3]^2 + 
   1/2 Log[3] Log[1 + Sqrt[3]] - 1/2 Log[1 + Sqrt[3]]^2 - 
   1/2 PolyLog[2, 1/3] + PolyLog[2, 1/Sqrt[3]], 
 PolyLog[2, -I (2 + Sqrt[3])] -> -((2 I Catalan)/3) - (29 Pi^2)/
   48 - 19/12 I Pi Log[2] + Log[2]^2/4 + 
   19/6 I Pi Log[1 + Sqrt[3]] - Log[2] Log[1 + Sqrt[3]] + 
   Log[1 + Sqrt[3]]^2 + 2 PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, I (2 + Sqrt[3])] -> (2 I Catalan)/3 - (29 Pi^2)/48 - 
   29/12 I Pi Log[2] + Log[2]^2/4 + 29/6 I Pi Log[1 + Sqrt[3]] -
    Log[2] Log[1 + Sqrt[3]] + Log[1 + Sqrt[3]]^2 + 
   2 PolyLog[2, 2 + Sqrt[3]], 
 PolyLog[2, E^(-((I Pi)/6))/Sqrt[3]] -> (5 Pi^2)/72 + (
   2 I Pi^2)/(9 Sqrt[3]) + 1/12 I Pi Log[3] - Log[3]^2/8 - (
   I PolyGamma[1, 1/3])/(3 Sqrt[3]), 
 PolyLog[2, 1/GoldenRatio^2] -> Pi^2/15 - Log[GoldenRatio]^2, 
 PolyLog[2, -(1/GoldenRatio)] -> -(Pi^2/15) + Log[GoldenRatio]^2/2,
  PolyLog[2, 1/GoldenRatio] -> Pi^2/10 - Log[GoldenRatio]^2, 
 PolyLog[2, -GoldenRatio] -> -(Pi^2/10) - Log[GoldenRatio]^2, 
 PolyLog[3, -3] -> -(1/3) Log[3]^3 + 2 PolyLog[3, 1/3] - (13 Zeta[3])/
   6, PolyLog[3, -1 - I] -> 1/4 PolyLog[3, 2 I] - PolyLog[3, 1 + I], 
 PolyLog[3, -1 + I] -> -(1/16) Pi^2 Log[2] - 1/96 Pi^2 Log[5] - 
   1/16 Log[2] Log[5]^2 + Log[5]^3/48 - 1/4 PolyLog[3, 2 I] - 
   1/16 PolyLog[3, 1/5] - 1/16 PolyLog[3, 4/5] + PolyLog[3, 1 + I] - (
   33 Zeta[3])/32, 
 PolyLog[3, -(7/8)] -> 1/4 PolyLog[3, 49/64] - PolyLog[3, 7/8], 
 PolyLog[3, -(4/5)] -> 
  1/3 Pi^2 Log[2] - (2 Log[2]^3)/3 - 1/3 Pi^2 Log[3] - 
   2 Log[2]^2 Log[3] - 4 Log[2] Log[3]^2 + (2 Log[3]^3)/3 + 
   1/6 Pi^2 Log[5] + Log[2]^2 Log[5] + 2 Log[2] Log[3] Log[5] + 
   Log[3]^2 Log[5] + Log[2] Log[5]^2 - (5 Log[5]^3)/6 + 
   2 PolyLog[3, 1/6] + 2 PolyLog[3, 1/5] - 4 PolyLog[3, 1/3] + 
   4 PolyLog[3, 2/5] - 4 PolyLog[3, 2/3] + 2 PolyLog[3, 5/6] - (
   3 Zeta[3])/2, 
 PolyLog[3, -(3/4)] -> 
  1/3 Pi^2 Log[2] + (4 Log[2]^3)/3 - 2 Log[2]^2 Log[3] - 
   1/6 Pi^2 Log[7] + 2 Log[2] Log[3] Log[7] - Log[2] Log[7]^2 - 
   1/2 Log[3] Log[7]^2 + Log[7]^3/3 - PolyLog[3, 3/7] - 
   PolyLog[3, 4/7] + Zeta[3], 
 PolyLog[3, -(5/7)] -> -(1/6) Pi^2 Log[2] + (27 Log[2]^3)/2 - 
   1/3 Pi^2 Log[3] + 5/2 Log[2]^2 Log[3] + 1/2 Log[2] Log[3]^2 + 
   Log[3]^3 - 1/3 Pi^2 Log[5] - 2 Log[2]^2 Log[5] - 
   Log[2] Log[3] Log[5] - 1/2 Log[3]^2 Log[5] - 3/2 Log[2] Log[5]^2 - 
   1/2 Log[3] Log[5]^2 + (2 Log[5]^3)/3 + 1/3 Pi^2 Log[7] - 
   9 Log[2]^2 Log[7] - Log[2] Log[3] Log[7] + 2 Log[2] Log[5] Log[7] +
    Log[3] Log[5] Log[7] + 2 Log[2] Log[7]^2 - 1/2 Log[3] Log[7]^2 - 
   1/2 Log[5] Log[7]^2 - 2/3 PolyLog[3, 1/8] - PolyLog[3, 1/7] - 
   PolyLog[3, 1/6] - 1/4 PolyLog[3, 9/49] - PolyLog[3, 1/5] + 
   PolyLog[3, 2/7] - 2 PolyLog[3, 1/3] - PolyLog[3, 2/5] - 
   PolyLog[3, 5/12] + 2 PolyLog[3, 3/7] + 2 PolyLog[3, 4/7] - 
   PolyLog[3, 3/5] - 2 PolyLog[3, 2/3] - 1/4 PolyLog[3, 49/64] - 
   PolyLog[3, 4/5] - PolyLog[3, 6/7] + (65 Zeta[3])/12, 
 PolyLog[3, -(2/3)] -> 
  1/6 Pi^2 Log[3] - 1/2 Log[2] Log[3]^2 + Log[3]^3/6 - 
   1/6 Pi^2 Log[5] + Log[2] Log[3] Log[5] - 1/2 Log[2] Log[5]^2 - 
   1/2 Log[3] Log[5]^2 + Log[5]^3/3 - PolyLog[3, 2/5] - 
   PolyLog[3, 3/5] + Zeta[3], 
 PolyLog[3, -(3/5)] -> -(1/4) Pi^2 Log[2] + Log[2]^3/2 - 
   2/3 Pi^2 Log[3] + 3/2 Log[2]^2 Log[3] + Log[2] Log[3]^2 + (
   2 Log[3]^3)/3 + 1/2 Pi^2 Log[5] - Log[2]^2 Log[5] - 
   Log[2] Log[3] Log[5] - Log[3]^2 Log[5] + 1/2 Log[3] Log[5]^2 - 
   PolyLog[3, 1/6] - 1/2 PolyLog[3, 1/5] - PolyLog[3, 2/5] + 
   2 PolyLog[3, 3/5] - PolyLog[3, 2/3] + 1/2 PolyLog[3, 4/5] - 
   2 PolyLog[3, 5/6] + (37 Zeta[3])/24, 
 PolyLog[3, -(1/2)] -> 
  1/6 Pi^2 Log[2] + Log[2]^3/6 - 1/6 Pi^2 Log[3] - 
   1/2 Log[2] Log[3]^2 + Log[3]^3/3 - PolyLog[3, 1/3] - 
   PolyLog[3, 2/3] + Zeta[3], 
 PolyLog[3, -(1/2) - I/2] -> -((5 I Pi^3)/128) - 
   7/192 Pi^2 Log[2] + (5 Log[2]^3)/192 - 1/96 Pi^2 Log[5] - 
   1/16 Log[2] Log[5]^2 + Log[5]^3/48 - 1/4 PolyLog[3, 2 I] - 
   1/16 PolyLog[3, 1/5] - 1/16 PolyLog[3, 4/5] + PolyLog[3, 1 + I] - 
   1/4 PolyLog[3, 1/Sqrt[2]] + 1/4 PolyLog[3, Sqrt[2]] - (33 Zeta[3])/
   32, PolyLog[3, -(1/2) + I/2] -> (5 I Pi^3)/128 + 
   7/64 Pi^2 Log[2] + Log[2]^3/64 + 1/4 PolyLog[3, 2 I] - 
   PolyLog[3, 1 + I] + 1/4 PolyLog[3, 1/Sqrt[2]] - 
   1/4 PolyLog[3, Sqrt[2]], 
 PolyLog[3, -(4/9)] -> -(2/3) Pi^2 Log[3] + 2 Log[2] Log[3]^2 - (
   2 Log[3]^3)/3 + 2/3 Pi^2 Log[5] - 4 Log[2] Log[3] Log[5] + 
   2 Log[2] Log[5]^2 + 2 Log[3] Log[5]^2 - (4 Log[5]^3)/3 + 
   1/4 PolyLog[3, 16/81] + 4 PolyLog[3, 2/5] + 4 PolyLog[3, 3/5] - 
   4 PolyLog[3, 2/3] - 4 Zeta[3], 
 PolyLog[3, -(3/7)] -> 1/4 PolyLog[3, 9/49] - PolyLog[3, 3/7], 
 PolyLog[3, -(2/5)] -> 
  1/6 Pi^2 Log[5] - 1/2 Log[2] Log[5]^2 + Log[5]^3/6 - 
   1/6 Pi^2 Log[7] + Log[2] Log[5] Log[7] - 1/2 Log[2] Log[7]^2 - 
   1/2 Log[5] Log[7]^2 + Log[7]^3/3 - PolyLog[3, 2/7] - 
   PolyLog[3, 5/7] + Zeta[3], 
 PolyLog[3, -(1/3)] -> 
  1/6 Pi^2 Log[3] - Log[3]^3/6 + 2 PolyLog[3, 1/3] - (13 Zeta[3])/
   6, PolyLog[3, -(2/7)] -> -(5/12) Pi^2 Log[2] - (3 Log[2]^3)/2 + 
   1/3 Pi^2 Log[3] + Log[2] Log[3]^2 - (2 Log[3]^3)/3 + 
   1/6 Pi^2 Log[7] + 1/2 Log[2] Log[7]^2 - Log[7]^3/6 + 
   1/3 PolyLog[3, 1/8] + PolyLog[3, 1/7] + 2 PolyLog[3, 1/3] + 
   PolyLog[3, 4/7] + 2 PolyLog[3, 2/3] - (45 Zeta[3])/8, 
 PolyLog[3, -(1/4)] -> 
  1/3 Pi^2 Log[2] + (4 Log[2]^3)/3 - 1/6 Pi^2 Log[5] - 
   Log[2] Log[5]^2 + Log[5]^3/3 - PolyLog[3, 1/5] - PolyLog[3, 4/5] + 
   Zeta[3], 
 PolyLog[3, -(1/5)] -> -(1/6) Pi^2 Log[2] + Log[2]^3/3 - 
   1/6 Pi^2 Log[3] + Log[2]^2 Log[3] + Log[2] Log[3]^2 + Log[3]^3/
   3 + 1/6 Pi^2 Log[5] - 1/2 Log[2]^2 Log[5] - 
   Log[2] Log[3] Log[5] - 1/2 Log[3]^2 Log[5] + Log[5]^3/6 - 
   PolyLog[3, 1/6] - PolyLog[3, 5/6] + Zeta[3], 
 PolyLog[3, -(1/6)] -> 
  1/6 Pi^2 Log[2] + Log[2]^3/6 + 1/6 Pi^2 Log[3] + 
   1/2 Log[2]^2 Log[3] + 1/2 Log[2] Log[3]^2 + Log[3]^3/6 - 
   1/6 Pi^2 Log[7] - 1/2 Log[2] Log[7]^2 - 1/2 Log[3] Log[7]^2 + 
   Log[7]^3/3 - PolyLog[3, 1/7] - PolyLog[3, 6/7] + Zeta[3], 
 PolyLog[3, -(1/7)] -> -(1/2) Pi^2 Log[2] + 9 Log[2]^3 + 
   1/6 Pi^2 Log[7] - 9/2 Log[2]^2 Log[7] + Log[7]^3/6 - 
   PolyLog[3, 1/8] - PolyLog[3, 7/8] + Zeta[3], 
 PolyLog[3, -(1/8)] -> 
  2 Pi^2 Log[2] + (9 Log[2]^3)/2 - 3 Pi^2 Log[3] - 
   9 Log[2] Log[3]^2 + 6 Log[3]^3 - 18 PolyLog[3, 1/3] - 
   18 PolyLog[3, 2/3] + (121 Zeta[3])/4, 
 PolyLog[3, -(1/9)] -> 
  1/6 Pi^2 Log[2] - Log[2]^3/3 + 1/3 Pi^2 Log[3] - 
   Log[2]^2 Log[3] - 2 Log[2] Log[3]^2 + (2 Log[3]^3)/3 - 
   1/6 Pi^2 Log[5] + 2 Log[2] Log[3] Log[5] - Log[3] Log[5]^2 + 
   Log[5]^3/3 + 2 PolyLog[3, 1/6] + PolyLog[3, 1/5] + 
   4 PolyLog[3, 1/3] - 2 PolyLog[3, 2/5] - 2 PolyLog[3, 3/5] - 
   2 PolyLog[3, 2/3] + PolyLog[3, 4/5] - (5 Zeta[3])/6, 
 PolyLog[3, -(I/10)] -> -((I Pi^3)/16) + 1/24 Pi^2 Log[2] - 
   1/4 I Pi Log[2]^2 + Log[2]^3/6 + 1/24 Pi^2 Log[5] - 
   1/2 I Pi Log[2] Log[5] + 1/2 Log[2]^2 Log[5] - 
   1/4 I Pi Log[5]^2 + 1/2 Log[2] Log[5]^2 + Log[5]^3/6 + 
   PolyLog[3, 10 I], 
 PolyLog[3, I/10] -> (I Pi^3)/16 + 1/24 Pi^2 Log[2] + 
   1/4 I Pi Log[2]^2 + Log[2]^3/6 + 1/24 Pi^2 Log[5] + 
   1/2 I Pi Log[2] Log[5] + 1/2 Log[2]^2 Log[5] + 
   1/4 I Pi Log[5]^2 + 1/2 Log[2] Log[5]^2 + Log[5]^3/6 + 
   PolyLog[3, -10 I], 
 PolyLog[3, -(I/9)] -> -((I Pi^3)/16) + 1/12 Pi^2 Log[3] - 
   I Pi Log[3]^2 + (4 Log[3]^3)/3 + PolyLog[3, 9 I], 
 PolyLog[3, I/9] -> (I Pi^3)/16 + 1/12 Pi^2 Log[3] + 
   I Pi Log[3]^2 + (4 Log[3]^3)/3 + PolyLog[3, -9 I], 
 PolyLog[3, -(I/8)] -> -((I Pi^3)/16) + 1/8 Pi^2 Log[2] - 
   9/4 I Pi Log[2]^2 + (9 Log[2]^3)/2 + PolyLog[3, 8 I], 
 PolyLog[3, I/8] -> (I Pi^3)/16 + 1/8 Pi^2 Log[2] + 
   9/4 I Pi Log[2]^2 + (9 Log[2]^3)/2 + PolyLog[3, -8 I], 
 PolyLog[3, -(I/6)] -> -((I Pi^3)/16) + 1/24 Pi^2 Log[2] - 
   1/4 I Pi Log[2]^2 + Log[2]^3/6 + 1/24 Pi^2 Log[3] - 
   1/2 I Pi Log[2] Log[3] + 1/2 Log[2]^2 Log[3] - 
   1/4 I Pi Log[3]^2 + 1/2 Log[2] Log[3]^2 + Log[3]^3/6 + 
   PolyLog[3, 6 I], 
 PolyLog[3, I/6] -> (I Pi^3)/16 + 1/24 Pi^2 Log[2] + 
   1/4 I Pi Log[2]^2 + Log[2]^3/6 + 1/24 Pi^2 Log[3] + 
   1/2 I Pi Log[2] Log[3] + 1/2 Log[2]^2 Log[3] + 
   1/4 I Pi Log[3]^2 + 1/2 Log[2] Log[3]^2 + Log[3]^3/6 + 
   PolyLog[3, -6 I], 
 PolyLog[3, -(I/5)] -> -((I Pi^3)/16) + 1/24 Pi^2 Log[5] - 
   1/4 I Pi Log[5]^2 + Log[5]^3/6 + PolyLog[3, 5 I], 
 PolyLog[3, I/5] -> (I Pi^3)/16 + 1/24 Pi^2 Log[5] + 
   1/4 I Pi Log[5]^2 + Log[5]^3/6 + PolyLog[3, -5 I], 
 PolyLog[3, -(I/4)] -> -((I Pi^3)/16) - 5/4 Pi^2 Log[2] + (
   3 Log[2]^3)/2 + PolyLog[3, 4 I] - 8 PolyLog[3, 1/Sqrt[2]] + 
   8 PolyLog[3, Sqrt[2]], 
 PolyLog[3, I/4] -> (I Pi^3)/16 + 17/12 Pi^2 Log[2] + (
   7 Log[2]^3)/6 + PolyLog[3, -4 I] + 8 PolyLog[3, 1/Sqrt[2]] - 
   8 PolyLog[3, Sqrt[2]], 
 PolyLog[3, -(I/3)] -> -((I Pi^3)/16) + 1/24 Pi^2 Log[3] - 
   1/4 I Pi Log[3]^2 + Log[3]^3/6 + PolyLog[3, 3 I], 
 PolyLog[3, I/3] -> (I Pi^3)/16 + 1/24 Pi^2 Log[2] - Log[2]^3/
   12 + 1/24 Pi^2 Log[3] - 1/4 Log[2]^2 Log[3] + 
   1/4 I Pi Log[3]^2 - 1/2 Log[2] Log[3]^2 - 1/24 Pi^2 Log[5] + 
   1/2 Log[2] Log[3] Log[5] - 1/4 Log[3] Log[5]^2 + Log[5]^3/12 - 
   PolyLog[3, 3 I] + 1/2 PolyLog[3, 1/6] + 1/4 PolyLog[3, 1/5] + 
   PolyLog[3, 1/3] - 1/2 PolyLog[3, 2/5] - 1/2 PolyLog[3, 3/5] - 
   1/2 PolyLog[3, 2/3] + 1/4 PolyLog[3, 4/5] - (5 Zeta[3])/24, 
 PolyLog[3, -(I/2)] -> -((I Pi^3)/16) - 7/24 Pi^2 Log[2] + (
   5 Log[2]^3)/24 + PolyLog[3, 2 I] - 2 PolyLog[3, 1/Sqrt[2]] + 
   2 PolyLog[3, Sqrt[2]], 
 PolyLog[3, I/2] -> (I Pi^3)/16 + 3/8 Pi^2 Log[2] + Log[2]^3/
   8 - 1/24 Pi^2 Log[5] - 1/4 Log[2] Log[5]^2 + Log[5]^3/12 - 
   PolyLog[3, 2 I] - 1/4 PolyLog[3, 1/5] - 1/4 PolyLog[3, 4/5] + 
   2 PolyLog[3, 1/Sqrt[2]] - 2 PolyLog[3, Sqrt[2]] + Zeta[3]/4, 
 PolyLog[3, -((2 I)/3)] -> -(1/6) Pi^2 Log[3] + 
   1/2 Log[2] Log[3]^2 - Log[3]^3/6 + 1/6 Pi^2 Log[5] - 
   Log[2] Log[3] Log[5] + 1/2 Log[2] Log[5]^2 + 1/2 Log[3] Log[5]^2 - 
   Log[5]^3/3 - PolyLog[3, (2 I)/3] + 1/16 PolyLog[3, 16/81] + 
   PolyLog[3, 2/5] + PolyLog[3, 3/5] - PolyLog[3, 2/3] - Zeta[3], 
 PolyLog[3, -((3 I)/4)] -> 
  1/12 Pi^2 Log[2] + (17 Log[2]^3)/6 + Pi^2 Log[3] - 
   7/2 Log[2]^2 Log[3] + 3 Log[2] Log[3]^2 - (4 Log[3]^3)/3 - 
   3/4 Pi^2 Log[5] + 3 Log[2] Log[3] Log[5] - 3 Log[2] Log[5]^2 - 
   3/2 Log[3] Log[5]^2 + (3 Log[5]^3)/2 - PolyLog[3, (3 I)/4] - 
   PolyLog[3, 1/6] - 3/2 PolyLog[3, 1/5] + 4 PolyLog[3, 1/3] - 
   3 PolyLog[3, 2/5] - 3 PolyLog[3, 3/5] + 5 PolyLog[3, 2/3] - 
   3/2 PolyLog[3, 4/5] + (5 Zeta[3])/24, 
 PolyLog[3, -I] -> -((I Pi^3)/32) - (3 Zeta[3])/32, 
 PolyLog[3, I] -> (I Pi^3)/32 - (3 Zeta[3])/32, 
 PolyLog[3, -2 I] -> -(1/24) Pi^2 Log[5] - 1/4 Log[2] Log[5]^2 + 
   Log[5]^3/12 - PolyLog[3, 2 I] - 1/4 PolyLog[3, 1/5] - 
   1/4 PolyLog[3, 4/5] + Zeta[3]/4, 
 PolyLog[3, -3 I] -> 
  1/24 Pi^2 Log[2] - Log[2]^3/12 - 1/4 Log[2]^2 Log[3] - 
   1/2 Log[2] Log[3]^2 - Log[3]^3/6 - 1/24 Pi^2 Log[5] + 
   1/2 Log[2] Log[3] Log[5] - 1/4 Log[3] Log[5]^2 + Log[5]^3/12 - 
   PolyLog[3, 3 I] + 1/2 PolyLog[3, 1/6] + 1/4 PolyLog[3, 1/5] + 
   PolyLog[3, 1/3] - 1/2 PolyLog[3, 2/5] - 1/2 PolyLog[3, 3/5] - 
   1/2 PolyLog[3, 2/3] + 1/4 PolyLog[3, 4/5] - (5 Zeta[3])/24, 
 PolyLog[3, -7 I] -> -(1/4) Pi^2 Log[2] + 18 Log[2]^3 - 
   1/2 Pi^2 Log[3] - 3/2 Log[2] Log[3]^2 + Log[3]^3 - 
   1/4 Pi^2 Log[5] - 3/2 Log[2] Log[5]^2 + Log[5]^3/2 + 
   1/3 Pi^2 Log[7] - 45/4 Log[2]^2 Log[7] + 3 Log[2] Log[7]^2 - (
   2 Log[7]^3)/3 - PolyLog[3, 7 I] - 3/2 PolyLog[3, 1/8] - 
   1/2 PolyLog[3, 1/7] - 3/2 PolyLog[3, 1/5] + 3 PolyLog[3, 2/7] - 
   3 PolyLog[3, 1/3] + 3/2 PolyLog[3, 4/7] - 3 PolyLog[3, 2/3] - 
   1/4 PolyLog[3, 49/64] - 3/2 PolyLog[3, 4/5] - 
   1/2 PolyLog[3, 7/8] + (91 Zeta[3])/16, 
 PolyLog[3, 1/26] -> 
  7/12 Pi^2 Log[2] + (65 Log[2]^3)/6 + 2 Pi^2 Log[3] - 
   8 Log[2]^2 Log[3] + 6 Log[2] Log[3]^2 - 4 Log[3]^3 - 
   6 Log[2] Log[5]^2 - Pi^2 Log[13] + 1/2 Log[2]^2 Log[13] + 
   2 Log[2] Log[3] Log[13] + 4 Log[2] Log[5] Log[13] + 
   4 Log[5]^2 Log[13] - 3 Log[2] Log[13]^2 - 4 Log[5] Log[13]^2 + (
   3 Log[13]^3)/2 + PolyLog[3, 1/13] - PolyLog[3, 3/16] - 
   8 PolyLog[3, 1/5] + 1/2 PolyLog[3, 4/13] + 12 PolyLog[3, 1/3] - 
   4 PolyLog[3, 5/13] - 4 PolyLog[3, 2/5] + 2 PolyLog[3, 13/25] - 
   2 PolyLog[3, 8/13] + 12 PolyLog[3, 2/3] - 1/2 PolyLog[3, 9/13] - 
   4 PolyLog[3, 10/13] - 4 PolyLog[3, 4/5] + PolyLog[3, 12/13] - (
   13 Zeta[3])/8, 
 PolyLog[3, 1/25] -> -(2/3) Pi^2 Log[2] + (4 Log[2]^3)/3 - 
   2/3 Pi^2 Log[3] + 4 Log[2]^2 Log[3] + 4 Log[2] Log[3]^2 + (
   4 Log[3]^3)/3 + 2/3 Pi^2 Log[5] - 2 Log[2]^2 Log[5] - 
   4 Log[2] Log[3] Log[5] - 2 Log[3]^2 Log[5] + (2 Log[5]^3)/3 - 
   4 PolyLog[3, 1/6] + 4 PolyLog[3, 1/5] - 4 PolyLog[3, 5/6] + 
   4 Zeta[3], 
 PolyLog[3, 1/22] -> 
  4/3 Pi^2 Log[2] - (5 Log[2]^3)/3 - 2/3 Pi^2 Log[3] - 
   4 Log[2]^2 Log[3] - 3 Log[2] Log[3]^2 + (10 Log[3]^3)/3 - 
   2/3 Pi^2 Log[7] + 2 Log[2]^2 Log[7] - 2 Log[2] Log[3] Log[7] + 
   Log[2] Log[7]^2 - 2 Log[3] Log[7]^2 + (4 Log[7]^3)/3 + 
   3 Log[2]^2 Log[11] + 2 Log[2] Log[3] Log[11] - Log[3]^2 Log[11] - 
   2 Log[2] Log[7] Log[11] + 2 Log[3] Log[7] Log[11] - 
   Log[7]^2 Log[11] - 2 PolyLog[3, 1/7] + 2 PolyLog[3, 2/11] - 
   2 PolyLog[3, 3/14] - 8 PolyLog[3, 1/3] - PolyLog[3, 11/18] - 
   6 PolyLog[3, 2/3] - PolyLog[3, 8/11] - 2 PolyLog[3, 11/14] - 
   2 PolyLog[3, 6/7] + 2 PolyLog[3, 11/12] + 17 Zeta[3], 
 PolyLog[3, 1/21] -> -(4/3) Pi^2 Log[2] + (179 Log[2]^3)/6 - 
   1/6 Pi^2 Log[3] - 1/2 Log[2]^2 Log[3] - 3/2 Log[2] Log[3]^2 - 
   1/3 Pi^2 Log[5] + Log[2] Log[3] Log[5] - 3/2 Log[2] Log[5]^2 - 
   1/2 Log[3] Log[5]^2 + (2 Log[5]^3)/3 + 5/6 Pi^2 Log[7] - 
   18 Log[2]^2 Log[7] - Log[2] Log[3] Log[7] + 1/2 Log[3]^2 Log[7] + 
   4 Log[2] Log[7]^2 + 1/2 Log[3] Log[7]^2 - Log[7]^3/2 - 
   8/3 PolyLog[3, 1/8] - PolyLog[3, 1/7] + PolyLog[3, 1/6] - 
   1/4 PolyLog[3, 9/49] - PolyLog[3, 1/5] + 3 PolyLog[3, 2/7] + 
   2 PolyLog[3, 1/3] - PolyLog[3, 2/5] + PolyLog[3, 3/7] + 
   2 PolyLog[3, 4/7] - PolyLog[3, 3/5] - 2 PolyLog[3, 2/3] - 
   1/4 PolyLog[3, 49/64] - PolyLog[3, 4/5] + PolyLog[3, 6/7] - 
   2 PolyLog[3, 7/8] + (11 Zeta[3])/6, 
 PolyLog[3, 1/16] -> 
  8/3 Pi^2 Log[2] + (32 Log[2]^3)/3 - 8/3 Pi^2 Log[3] - 
   8 Log[2] Log[3]^2 + (16 Log[3]^3)/3 - 2/3 Pi^2 Log[5] - 
   4 Log[2] Log[5]^2 + (4 Log[5]^3)/3 - 4 PolyLog[3, 1/5] - 
   16 PolyLog[3, 1/3] - 16 PolyLog[3, 2/3] - 4 PolyLog[3, 4/5] + 
   34 Zeta[3], 
 PolyLog[3, 1/15] -> 
  1/2 Pi^2 Log[2] + Log[2]^3 + 2/3 Pi^2 Log[3] + 
   Log[2]^2 Log[3] - Log[3]^3/3 - Log[2]^2 Log[5] + Log[3]^2 Log[5] - 
   2/3 Pi^2 Log[7] + 2 Log[2] Log[5] Log[7] - 2 Log[2] Log[7]^2 - 
   Log[3] Log[7]^2 - Log[5] Log[7]^2 + (4 Log[7]^3)/3 - 
   2 PolyLog[3, 1/7] + 2 PolyLog[3, 1/5] - 2 PolyLog[3, 2/7] + 
   2 PolyLog[3, 1/3] - PolyLog[3, 5/12] - PolyLog[3, 3/5] - 
   2 PolyLog[3, 5/7] + 2 PolyLog[3, 5/6] - 2 PolyLog[3, 6/7] + (
   15 Zeta[3])/4, 
 PolyLog[3, 1/10] -> -(1/4) Pi^2 Log[2] + (3 Log[2]^3)/2 - 
   4/3 Pi^2 Log[3] + 4 Log[2]^2 Log[3] + 2 Log[2] Log[3]^2 + (
   8 Log[3]^3)/3 + 1/3 Pi^2 Log[5] - 3/2 Log[2]^2 Log[5] - 
   4 Log[2] Log[3] Log[5] - 2 Log[3]^2 Log[5] + (5 Log[5]^3)/6 - 
   4 PolyLog[3, 1/6] - 5/2 PolyLog[3, 1/5] - 4 PolyLog[3, 1/3] - 
   2 PolyLog[3, 2/5] - 4 PolyLog[3, 2/3] + 1/2 PolyLog[3, 4/5] - 
   4 PolyLog[3, 5/6] + (129 Zeta[3])/8, 
 PolyLog[3, 1/9] -> 
  2/3 Pi^2 Log[3] - (2 Log[3]^3)/3 + 12 PolyLog[3, 1/3] - (
   26 Zeta[3])/3, 
 PolyLog[3, 3/25] -> 
  1/2 Pi^2 Log[2] + Log[2]^3 + Log[2]^2 Log[3] + 
   2/3 Pi^2 Log[5] - Log[3] Log[5]^2 + (2 Log[5]^3)/3 - 
   2/3 Pi^2 Log[11] + 2 Log[2] Log[5] Log[11] + 
   2 Log[3] Log[5] Log[11] - 2 Log[2] Log[11]^2 - Log[3] Log[11]^2 - 
   2 Log[5] Log[11]^2 + (4 Log[11]^3)/3 - PolyLog[3, 1/12] - 
   2 PolyLog[3, 1/11] + 2 PolyLog[3, 1/6] + 2 PolyLog[3, 1/5] - 
   PolyLog[3, 1/3] - 2 PolyLog[3, 5/11] - 2 PolyLog[3, 6/11] + 
   2 PolyLog[3, 3/5] - 2 PolyLog[3, 10/11] + (15 Zeta[3])/4, 
 PolyLog[3, 4/25] -> 
  2/3 Pi^2 Log[5] - 2 Log[2] Log[5]^2 + (2 Log[5]^3)/3 - 
   2/3 Pi^2 Log[7] + 4 Log[2] Log[5] Log[7] - 2 Log[2] Log[7]^2 - 
   2 Log[5] Log[7]^2 + (4 Log[7]^3)/3 - 4 PolyLog[3, 2/7] + 
   4 PolyLog[3, 2/5] - 4 PolyLog[3, 5/7] + 4 Zeta[3], 
 PolyLog[3, 2/9] -> 
  5/4 Pi^2 Log[2] + (9 Log[2]^3)/2 - 2/3 Pi^2 Log[3] - 
   5 Log[2] Log[3]^2 + (10 Log[3]^3)/3 - 2/3 Pi^2 Log[7] + 
   4 Log[2] Log[3] Log[7] - 3 Log[2] Log[7]^2 - 2 Log[3] Log[7]^2 + (
   4 Log[7]^3)/3 - PolyLog[3, 1/8] - 2 PolyLog[3, 1/7] - 
   6 PolyLog[3, 1/3] - 2 PolyLog[3, 3/7] - 2 PolyLog[3, 4/7] - 
   6 PolyLog[3, 2/3] - 2 PolyLog[3, 6/7] + (143 Zeta[3])/8, 
 PolyLog[3, 5/21] -> -(9/4) Pi^2 Log[2] + (94 Log[2]^3)/3 - 
   5/6 Pi^2 Log[3] + 6 Log[2]^2 Log[3] + 9/2 Log[2] Log[3]^2 + (
   4 Log[3]^3)/3 + 1/6 Pi^2 Log[5] - 7/2 Log[2]^2 Log[5] - 
   4 Log[2] Log[3] Log[5] - 3 Log[3]^2 Log[5] - 3/2 Log[2] Log[5]^2 + 
   Log[3] Log[5]^2 + (7 Log[5]^3)/6 + 2/3 Pi^2 Log[7] - 
   37/2 Log[2]^2 Log[7] - 2 Log[2] Log[3] Log[7] + 
   1/2 Log[3]^2 Log[7] + 2 Log[2] Log[5] Log[7] - 
   1/2 Log[5]^2 Log[7] + 3 Log[2] Log[7]^2 - 7/3 PolyLog[3, 1/8] - 
   2 PolyLog[3, 1/7] - 4 PolyLog[3, 1/6] - 9/2 PolyLog[3, 1/5] + 
   3 PolyLog[3, 1/3] - 3 PolyLog[3, 2/5] - PolyLog[3, 5/12] - 
   PolyLog[3, 3/7] + 3 PolyLog[3, 4/7] + 2 PolyLog[3, 3/5] - 
   PolyLog[3, 2/3] - PolyLog[3, 7/10] + PolyLog[3, 5/7] - 
   1/4 PolyLog[3, 49/64] - 1/2 PolyLog[3, 4/5] - 4 PolyLog[3, 5/6] - 
   2 PolyLog[3, 7/8] + (305 Zeta[3])/24, 
 PolyLog[3, 1/4] -> 
  1/3 Pi^2 Log[2] + (4 Log[2]^3)/3 - 2/3 Pi^2 Log[3] - 
   2 Log[2] Log[3]^2 + (4 Log[3]^3)/3 - 4 PolyLog[3, 1/3] - 
   4 PolyLog[3, 2/3] + (15 Zeta[3])/2, 
 PolyLog[3, 5/18] -> 
  1/4 Pi^2 Log[2] + (23 Log[2]^3)/2 + 4/3 Pi^2 Log[3] - 
   5 Log[2]^2 Log[3] + 7 Log[2] Log[3]^2 - (2 Log[3]^3)/3 - 
   Log[2]^2 Log[5] - 4 Log[2] Log[3] Log[5] - 2 Log[3]^2 Log[5] - 
   3 Log[2] Log[5]^2 + Log[3] Log[5]^2 + Log[5]^3 - 
   2/3 Pi^2 Log[13] + 5 Log[2] Log[3] Log[13] + 
   3 Log[2] Log[5] Log[13] + Log[3] Log[5] Log[13] - 
   4 Log[2] Log[13]^2 - 2 Log[3] Log[13]^2 - Log[5] Log[13]^2 + (
   4 Log[13]^3)/3 - PolyLog[3, 1/13] - PolyLog[3, 2/15] - 
   3 PolyLog[3, 1/6] - PolyLog[3, 3/16] - 3 PolyLog[3, 1/5] - 
   PolyLog[3, 3/13] - PolyLog[3, 4/13] + 10 PolyLog[3, 1/3] - 
   PolyLog[3, 5/13] - PolyLog[3, 2/5] + PolyLog[3, 3/5] - 
   PolyLog[3, 8/13] + 7 PolyLog[3, 2/3] - PolyLog[3, 9/13] - 
   PolyLog[3, 10/13] - 2 PolyLog[3, 4/5] - PolyLog[3, 5/6] - 
   PolyLog[3, 12/13] + (3 Zeta[3])/8, 
 PolyLog[3, 7/25] -> -(1/2) Pi^2 Log[2] + (82 Log[2]^3)/
   3 - Pi^2 Log[3] + 7 Log[2]^2 Log[3] + 3 Log[2] Log[3]^2 + (
   8 Log[3]^3)/3 - 6 Log[2]^2 Log[5] - 4 Log[2] Log[3] Log[5] - 
   2 Log[3]^2 Log[5] - 3 Log[2] Log[5]^2 - Log[3] Log[5]^2 + 
   2 Log[5]^3 + 1/3 Pi^2 Log[7] - 17 Log[2]^2 Log[7] - 
   2 Log[2] Log[3] Log[7] + 4 Log[2] Log[5] Log[7] + 
   2 Log[3] Log[5] Log[7] - Log[5]^2 Log[7] + 4 Log[2] Log[7]^2 - 
   Log[3] Log[7]^2 - Log[7]^3/3 - 4/3 PolyLog[3, 1/8] - 
   3 PolyLog[3, 1/7] - 4 PolyLog[3, 1/6] - 1/2 PolyLog[3, 9/49] - 
   2 PolyLog[3, 1/5] + 4 PolyLog[3, 2/7] - 4 PolyLog[3, 1/3] - 
   2 PolyLog[3, 5/12] + 4 PolyLog[3, 3/7] + 3 PolyLog[3, 4/7] - 
   2 PolyLog[3, 3/5] - 4 PolyLog[3, 2/3] + 2 PolyLog[3, 7/10] - 
   1/2 PolyLog[3, 49/64] - 2 PolyLog[3, 4/5] - 2 PolyLog[3, 5/6] - 
   2 PolyLog[3, 6/7] + (151 Zeta[3])/12, 
 PolyLog[3, 3/10] -> -(1/6) Pi^2 Log[2] + Log[2]^3/3 - 
   1/2 Log[2]^2 Log[3] - 1/6 Pi^2 Log[5] + Log[2]^2 Log[5] - 
   Log[2] Log[3] Log[5] + Log[2] Log[5]^2 - 1/2 Log[3] Log[5]^2 + 
   Log[5]^3/3 + 1/6 Pi^2 Log[7] - 1/2 Log[2]^2 Log[7] + 
   Log[2] Log[3] Log[7] - Log[2] Log[5] Log[7] + 
   Log[3] Log[5] Log[7] - 1/2 Log[5]^2 Log[7] - 1/2 Log[3] Log[7]^2 + 
   Log[7]^3/6 - 1/4 PolyLog[3, 9/49] + PolyLog[3, 3/7] - 
   PolyLog[3, 7/10] + Zeta[3], 
 PolyLog[3, 5/16] -> 
  1/2 Pi^2 Log[2] + 9 Log[2]^3 - 4/3 Pi^2 Log[3] - 
   3 Log[2]^2 Log[3] - 6 Log[2] Log[3]^2 + (7 Log[3]^3)/3 + 
   1/3 Pi^2 Log[5] - 15/2 Log[2]^2 Log[5] + 
   2 Log[2] Log[3] Log[5] + 4 Log[2] Log[5]^2 - Log[3] Log[5]^2 - (
   7 Log[5]^3)/6 + Log[2] Log[3] Log[11] + Log[2] Log[5] Log[11] + 
   Log[3] Log[5] Log[11] - Log[2] Log[11]^2 + PolyLog[3, 1/12] + 
   PolyLog[3, 1/11] + PolyLog[3, 1/6] + PolyLog[3, 2/11] + 
   7/2 PolyLog[3, 1/5] + PolyLog[3, 4/15] - PolyLog[3, 3/11] - 
   8 PolyLog[3, 1/3] + PolyLog[3, 2/5] - PolyLog[3, 5/11] - 
   PolyLog[3, 6/11] - PolyLog[3, 3/5] - 10 PolyLog[3, 2/3] - 
   PolyLog[3, 8/11] + 5/2 PolyLog[3, 4/5] + PolyLog[3, 9/11] + 
   PolyLog[3, 5/6] + PolyLog[3, 10/11] + (115 Zeta[3])/12, 
 PolyLog[3, 7/22] -> -(1/12) Pi^2 Log[2] - (53 Log[2]^3)/3 + 
   5/6 Pi^2 Log[3] - 5/2 Log[2]^2 Log[3] + 5/2 Log[2] Log[3]^2 - (
   2 Log[3]^3)/3 + 1/3 Pi^2 Log[5] - Log[2] Log[3] Log[5] + 
   3/2 Log[2] Log[5]^2 + 1/2 Log[3] Log[5]^2 - (2 Log[5]^3)/3 + 
   1/2 Pi^2 Log[7] + 7 Log[2]^2 Log[7] - Log[2] Log[3] Log[7] - 
   5/2 Log[3]^2 Log[7] - 2 Log[2] Log[7]^2 + 3/2 Log[3] Log[7]^2 - (
   5 Log[7]^3)/6 - 2/3 Pi^2 Log[11] + 3 Log[2]^2 Log[11] + 
   Log[3]^2 Log[11] + Log[2] Log[7] Log[11] + Log[3] Log[7] Log[11] + 
   Log[7]^2 Log[11] - Log[3] Log[11]^2 - Log[7] Log[11]^2 + Log[11]^3/
   3 + PolyLog[3, 1/12] + PolyLog[3, 1/11] + 4/3 PolyLog[3, 1/8] + 
   2 PolyLog[3, 1/7] + 1/4 PolyLog[3, 9/49] + PolyLog[3, 1/5] + 
   PolyLog[3, 3/14] + PolyLog[3, 3/11] - 2 PolyLog[3, 2/7] + 
   4 PolyLog[3, 1/3] - PolyLog[3, 7/18] + PolyLog[3, 2/5] - 
   PolyLog[3, 3/7] + PolyLog[3, 11/21] - PolyLog[3, 6/11] - 
   PolyLog[3, 4/7] + PolyLog[3, 3/5] - PolyLog[3, 7/11] + 
   5 PolyLog[3, 2/3] + 1/4 PolyLog[3, 49/64] + PolyLog[3, 11/14] + 
   PolyLog[3, 4/5] - PolyLog[3, 9/11] + 2 PolyLog[3, 6/7] + 
   PolyLog[3, 11/12] - (101 Zeta[3])/8, 
 PolyLog[3, 5/14] -> 
  5/4 Pi^2 Log[2] - (17 Log[2]^3)/2 - 1/2 Log[2]^2 Log[3] - 
   3 Log[2] Log[3]^2 + Log[3]^3/3 + 1/6 Pi^2 Log[5] - 
   3/2 Log[2]^2 Log[5] + 2 Log[2] Log[3] Log[5] + Log[3]^2 Log[5] + 
   Log[2] Log[5]^2 - 1/2 Log[3] Log[5]^2 - (5 Log[5]^3)/6 - 
   1/2 Pi^2 Log[7] + 11/2 Log[2]^2 Log[7] - Log[2] Log[3] Log[7] + 
   Log[2] Log[5] Log[7] + Log[3] Log[5] Log[7] + 1/2 Log[5]^2 Log[7] -
    Log[2] Log[7]^2 - 1/2 Log[3] Log[7]^2 - Log[5] Log[7]^2 + 
   Log[7]^3/2 + PolyLog[3, 1/8] + PolyLog[3, 1/7] + 
   2 PolyLog[3, 1/6] - 1/4 PolyLog[3, 9/49] + 5/2 PolyLog[3, 1/5] - 
   3 PolyLog[3, 1/3] + 2 PolyLog[3, 2/5] - PolyLog[3, 5/12] + 
   2 PolyLog[3, 3/7] - PolyLog[3, 4/7] - PolyLog[3, 3/5] - 
   3 PolyLog[3, 2/3] + PolyLog[3, 7/10] - PolyLog[3, 5/7] + 
   1/2 PolyLog[3, 4/5] + 3 PolyLog[3, 5/6] - PolyLog[3, 6/7] + 
   PolyLog[3, 7/8] - (41 Zeta[3])/24, 
 PolyLog[3, 9/25] -> -Pi^2 Log[2] + 2 Log[2]^3 - 
   8/3 Pi^2 Log[3] + 6 Log[2]^2 Log[3] + 4 Log[2] Log[3]^2 + (
   8 Log[3]^3)/3 + 2 Pi^2 Log[5] - 4 Log[2]^2 Log[5] - 
   4 Log[2] Log[3] Log[5] - 4 Log[3]^2 Log[5] + 2 Log[3] Log[5]^2 - 
   4 PolyLog[3, 1/6] - 2 PolyLog[3, 1/5] - 4 PolyLog[3, 2/5] + 
   12 PolyLog[3, 3/5] - 4 PolyLog[3, 2/3] + 2 PolyLog[3, 4/5] - 
   8 PolyLog[3, 5/6] + (37 Zeta[3])/6, 
 PolyLog[3, 3/8] -> -(1/3) Pi^2 Log[2] + (14 Log[2]^3)/3 + 
   4/3 Pi^2 Log[3] - 4 Log[2]^2 Log[3] + 4 Log[2] Log[3]^2 - 
   2 Log[3]^3 - 2/3 Pi^2 Log[5] + 2 Log[2] Log[3] Log[5] - 
   3 Log[2] Log[5]^2 - Log[3] Log[5]^2 + (4 Log[5]^3)/3 - 
   PolyLog[3, 1/6] - 2 PolyLog[3, 1/5] + 6 PolyLog[3, 1/3] - 
   2 PolyLog[3, 2/5] - 2 PolyLog[3, 3/5] + 7 PolyLog[3, 2/3] - 
   2 PolyLog[3, 4/5] - (19 Zeta[3])/6, 
 PolyLog[3, 7/16] -> -(1/3) Pi^2 Log[2] + (86 Log[2]^3)/3 - 
   8/3 Pi^2 Log[3] - 8 Log[2] Log[3]^2 + (16 Log[3]^3)/3 + 
   2/3 Pi^2 Log[7] - 17 Log[2]^2 Log[7] + 4 Log[2] Log[7]^2 - 
   Log[7]^3/3 - 2 PolyLog[3, 1/8] - 2 PolyLog[3, 1/7] - 
   16 PolyLog[3, 1/3] + 4 PolyLog[3, 4/7] - 16 PolyLog[3, 2/3] - 
   2 PolyLog[3, 7/8] + (57 Zeta[3])/2, 
 PolyLog[3, 11/25] -> 
  2/3 Pi^2 Log[5] + 2 Log[2] Log[3] Log[5] - 2 Log[3]^2 Log[5] + (
   2 Log[5]^3)/3 - 2/3 Pi^2 Log[7] - 2 Log[2] Log[3] Log[7] + 
   2 Log[3]^2 Log[7] + 2 Log[2] Log[5] Log[7] - 
   2 Log[3] Log[5] Log[7] - 2 Log[2] Log[7]^2 + 2 Log[3] Log[7]^2 - 
   2 Log[5] Log[7]^2 + (4 Log[7]^3)/3 - 2 Log[2] Log[5] Log[11] + 
   2 Log[3] Log[5] Log[11] - Log[5]^2 Log[11] + 
   2 Log[2] Log[7] Log[11] - 2 Log[3] Log[7] Log[11] + 
   2 Log[5] Log[7] Log[11] - Log[7]^2 Log[11] - 2 PolyLog[3, 2/7] - 
   PolyLog[3, 4/11] - 2 PolyLog[3, 10/21] - 2 PolyLog[3, 11/21] + 
   2 PolyLog[3, 6/11] + 2 PolyLog[3, 3/5] + 2 PolyLog[3, 2/3] - 
   2 PolyLog[3, 5/7] + 2 PolyLog[3, 11/15] - PolyLog[3, 9/11] + 
   2 Zeta[3], 
 PolyLog[3, 4/9] -> 
  2/3 Pi^2 Log[3] - 2 Log[2] Log[3]^2 + (2 Log[3]^3)/3 - 
   2/3 Pi^2 Log[5] + 4 Log[2] Log[3] Log[5] - 2 Log[2] Log[5]^2 - 
   2 Log[3] Log[5]^2 + (4 Log[5]^3)/3 - 4 PolyLog[3, 2/5] - 
   4 PolyLog[3, 3/5] + 4 PolyLog[3, 2/3] + 4 Zeta[3], 
 PolyLog[3, 9/20] -> 
  1/6 Pi^2 Log[2] + (5 Log[2]^3)/3 + 4/3 Pi^2 Log[3] - 
   5 Log[2]^2 Log[3] - (5 Log[3]^3)/3 + 1/3 Pi^2 Log[5] + 
   7/2 Log[2]^2 Log[5] - 4 Log[2] Log[3] Log[5] + 2 Log[3]^2 Log[5] + 
   2 Log[2] Log[5]^2 + Log[3] Log[5]^2 - (7 Log[5]^3)/6 - 
   2/3 Pi^2 Log[11] + 5 Log[2] Log[3] Log[11] + 
   Log[2] Log[5] Log[11] + Log[3] Log[5] Log[11] - 
   3 Log[2] Log[11]^2 - 2 Log[3] Log[11]^2 - Log[5] Log[11]^2 + (
   4 Log[11]^3)/3 - PolyLog[3, 1/12] - PolyLog[3, 1/11] + 
   3 PolyLog[3, 1/6] - PolyLog[3, 2/11] + 3/2 PolyLog[3, 1/5] - 
   PolyLog[3, 4/15] - PolyLog[3, 3/11] + 5 PolyLog[3, 2/5] - 
   PolyLog[3, 5/11] - PolyLog[3, 6/11] + 3 PolyLog[3, 3/5] + 
   6 PolyLog[3, 2/3] - PolyLog[3, 8/11] - 1/2 PolyLog[3, 4/5] - 
   PolyLog[3, 9/11] + 3 PolyLog[3, 5/6] - PolyLog[3, 10/11] - (
   37 Zeta[3])/4, 
 PolyLog[3, 7/15] -> 
  1/2 Pi^2 Log[2] + (9 Log[2]^3)/2 - 1/6 Pi^2 Log[3] - 
   1/2 Log[2]^2 Log[3] - 3/2 Log[2] Log[3]^2 + Log[3]^3/
   3 - Pi^2 Log[5] + Log[2]^2 Log[5] + Log[3]^2 Log[5] - 
   3/2 Log[2] Log[5]^2 - 1/2 Log[3] Log[5]^2 + Log[5]^3 + 
   5/6 Pi^2 Log[7] - 5 Log[2]^2 Log[7] - 1/2 Log[3]^2 Log[7] - 
   Log[5]^2 Log[7] + 3 Log[2] Log[7]^2 + 1/2 Log[3] Log[7]^2 + 
   Log[5] Log[7]^2 - (7 Log[7]^3)/6 - 1/4 PolyLog[3, 9/49] + 
   2 PolyLog[3, 2/7] + 3 PolyLog[3, 3/7] + 2 PolyLog[3, 4/7] - 
   2 PolyLog[3, 3/5] - 2 PolyLog[3, 2/3] - PolyLog[3, 7/10] + 
   2 PolyLog[3, 5/7] - 1/4 PolyLog[3, 49/64] - 2 PolyLog[3, 4/5] + 
   PolyLog[3, 5/6] + PolyLog[3, 7/8] - (7 Zeta[3])/4, 
 PolyLog[3, 12/25] -> 
  1/2 Pi^2 Log[2] + 11 Log[2]^3 + 2 Pi^2 Log[3] - 
   7 Log[2]^2 Log[3] + 6 Log[2] Log[3]^2 - 3 Log[3]^3 - 
   2/3 Pi^2 Log[5] + 2 Log[2] Log[3] Log[5] - 8 Log[2] Log[5]^2 - 
   3 Log[3] Log[5]^2 + (10 Log[5]^3)/3 - 2/3 Pi^2 Log[13] + 
   2 Log[2] Log[3] Log[13] + 6 Log[2] Log[5] Log[13] + 
   2 Log[3] Log[5] Log[13] - 4 Log[2] Log[13]^2 - Log[3] Log[13]^2 - 
   2 Log[5] Log[13]^2 + (4 Log[13]^3)/3 - 2 PolyLog[3, 1/6] - 
   PolyLog[3, 3/16] - 4 PolyLog[3, 1/5] - 2 PolyLog[3, 3/13] + 
   10 PolyLog[3, 1/3] - 2 PolyLog[3, 5/13] - 4 PolyLog[3, 2/5] - 
   2 PolyLog[3, 3/5] - 2 PolyLog[3, 8/13] + 10 PolyLog[3, 2/3] - 
   2 PolyLog[3, 10/13] - 2 PolyLog[3, 4/5] + (7 Zeta[3])/4, 
 PolyLog[3, 1/2 - I/2] -> -((7 I Pi^3)/128) - 
   35/192 Pi^2 Log[2] + (7 Log[2]^3)/192 + PolyLog[3, 1 + I] - 
   3/4 PolyLog[3, 1/Sqrt[2]] + 3/4 PolyLog[3, Sqrt[2]], 
 PolyLog[3, 1/2 + I/2] -> (7 I Pi^3)/128 + 25/192 Pi^2 Log[2] + 
   Log[2]^3/192 - PolyLog[3, 1 + I] + 3/4 PolyLog[3, 1/Sqrt[2]] - 
   3/4 PolyLog[3, Sqrt[2]] + (35 Zeta[3])/32, 
 PolyLog[3, 8/15] -> 
  1/2 Log[2]^2 Log[3] + 5/6 Pi^2 Log[5] - Log[2]^2 Log[5] - 
   3 Log[2] Log[3] Log[5] + 3/2 Log[3] Log[5]^2 - (2 Log[5]^3)/3 - 
   5/6 Pi^2 Log[7] + 1/2 Log[2]^2 Log[7] + 
   3 Log[2] Log[3] Log[7] + 3 Log[2] Log[5] Log[7] - 
   Log[3] Log[5] Log[7] + 1/2 Log[5]^2 Log[7] - 3 Log[2] Log[7]^2 - 
   1/2 Log[3] Log[7]^2 - Log[5] Log[7]^2 + (7 Log[7]^3)/6 + 
   1/4 PolyLog[3, 9/49] - 2 PolyLog[3, 2/7] - 3 PolyLog[3, 3/7] - 
   2 PolyLog[3, 4/7] + 2 PolyLog[3, 3/5] + 2 PolyLog[3, 2/3] + 
   PolyLog[3, 7/10] - 2 PolyLog[3, 5/7] + 2 PolyLog[3, 4/5] - 
   PolyLog[3, 5/6] + (11 Zeta[3])/4, 
 PolyLog[3, 11/20] -> -(5/6) Pi^2 Log[2] + (11 Log[2]^3)/3 - 
   4/3 Pi^2 Log[3] + 5 Log[2]^2 Log[3] + 2 Log[2] Log[3]^2 + (
   7 Log[3]^3)/3 - 1/3 Pi^2 Log[5] + 1/2 Log[2]^2 Log[5] - 
   4 Log[2] Log[3] Log[5] - Log[3]^2 Log[5] + (7 Log[5]^3)/6 + 
   2/3 Pi^2 Log[11] - 4 Log[2]^2 Log[11] + Log[2] Log[3] Log[11] - 
   Log[3]^2 Log[11] - Log[2] Log[5] Log[11] - Log[5]^2 Log[11] + 
   Log[2] Log[11]^2 + Log[5] Log[11]^2 - Log[11]^3/3 + 
   PolyLog[3, 1/11] - 3 PolyLog[3, 1/6] - PolyLog[3, 2/11] - 
   3/2 PolyLog[3, 1/5] - PolyLog[3, 3/11] - 2 PolyLog[3, 1/3] - 
   3 PolyLog[3, 2/5] + PolyLog[3, 5/11] - PolyLog[3, 6/11] - 
   PolyLog[3, 3/5] - 4 PolyLog[3, 2/3] + PolyLog[3, 8/11] - 
   PolyLog[3, 11/15] + 1/2 PolyLog[3, 4/5] + PolyLog[3, 9/11] - 
   3 PolyLog[3, 5/6] + PolyLog[3, 10/11] - PolyLog[3, 11/12] + (
   175 Zeta[3])/12, 
 PolyLog[3, 5/9] -> -(1/3) Pi^2 Log[2] + (2 Log[2]^3)/3 - 
   2/3 Pi^2 Log[3] + 2 Log[2]^2 Log[3] + 2 Log[2] Log[3]^2 + (
   4 Log[3]^3)/3 + 2/3 Pi^2 Log[5] - Log[2]^2 Log[5] - 
   2 Log[2] Log[3] Log[5] - 3 Log[3]^2 Log[5] + 2 Log[3] Log[5]^2 - 
   Log[5]^3/3 - 2 PolyLog[3, 1/6] - 2 PolyLog[3, 1/5] + 
   4 PolyLog[3, 1/3] + 4 PolyLog[3, 3/5] - 2 PolyLog[3, 5/6] - (
   3 Zeta[3])/2, 
 PolyLog[3, 14/25] -> (31 Log[2]^3)/3 - 2/3 Pi^2 Log[3] - 
   Log[2]^2 Log[3] - 3 Log[2] Log[3]^2 - Pi^2 Log[5] + 
   4 Log[2] Log[3] Log[5] - Log[2] Log[5]^2 - 3 Log[3] Log[5]^2 + 
   2 Log[5]^3 + 1/3 Pi^2 Log[7] - 4 Log[2]^2 Log[7] + 
   4 Log[2] Log[3] Log[7] + Log[3]^2 Log[7] - 
   2 Log[2] Log[5] Log[7] + 2 Log[3] Log[5] Log[7] - 
   2 Log[5]^2 Log[7] + 2 Log[2] Log[7]^2 - 3 Log[3] Log[7]^2 + 
   2 Log[5] Log[7]^2 - Log[7]^3/3 + 2/3 Pi^2 Log[11] - 
   4 Log[2] Log[3] Log[11] - 4 Log[2] Log[7] Log[11] + 
   3 Log[2] Log[11]^2 + 2 Log[3] Log[11]^2 + Log[7] Log[11]^2 - (
   4 Log[11]^3)/3 - 4/3 PolyLog[3, 1/8] - 2 PolyLog[3, 1/7] + 
   2 PolyLog[3, 2/11] - 1/2 PolyLog[3, 9/49] + 2 PolyLog[3, 4/15] + 
   4 PolyLog[3, 2/7] - 4 PolyLog[3, 1/3] + 2 PolyLog[3, 4/11] + 
   PolyLog[3, 7/18] - 2 PolyLog[3, 2/5] + 2 PolyLog[3, 3/7] + 
   2 PolyLog[3, 10/21] - 4 PolyLog[3, 3/5] + 2 PolyLog[3, 7/11] - 
   8 PolyLog[3, 2/3] + 2 PolyLog[3, 5/7] + 2 PolyLog[3, 9/11] - 
   2 PolyLog[3, 6/7] - PolyLog[3, 7/8] + (29 Zeta[3])/6, 
 PolyLog[3, 9/16] -> -(4/3) Pi^2 Log[2] + (32 Log[2]^3)/3 + 
   8/3 Pi^2 Log[3] - 16 Log[2]^2 Log[3] + 8 Log[2] Log[3]^2 - 
   4 Log[3]^3 - 2/3 Pi^2 Log[7] + 8 Log[2] Log[3] Log[7] - 
   4 Log[2] Log[7]^2 - 2 Log[3] Log[7]^2 + (4 Log[7]^3)/3 + 
   8 PolyLog[3, 1/3] - 4 PolyLog[3, 3/7] - 4 PolyLog[3, 4/7] + 
   16 PolyLog[3, 2/3] - (40 Zeta[3])/3, 
 PolyLog[3, 7/12] -> -(1/6) Pi^2 Log[2] - (65 Log[2]^3)/6 + 
   1/6 Pi^2 Log[3] + 3/2 Log[2]^2 Log[3] + 3/2 Log[2] Log[3]^2 - (
   2 Log[3]^3)/3 + 1/3 Pi^2 Log[5] - Log[2] Log[3] Log[5] + 
   3/2 Log[2] Log[5]^2 + 1/2 Log[3] Log[5]^2 - (2 Log[5]^3)/3 - 
   1/6 Pi^2 Log[7] + 7 Log[2]^2 Log[7] - Log[2] Log[3] Log[7] - 
   1/2 Log[3]^2 Log[7] - 2 Log[2] Log[7]^2 + 1/2 Log[3] Log[7]^2 + 
   Log[7]^3/6 + 2/3 PolyLog[3, 1/8] + PolyLog[3, 1/7] + 
   PolyLog[3, 1/6] + 1/4 PolyLog[3, 9/49] + PolyLog[3, 1/5] - 
   PolyLog[3, 2/7] + 2 PolyLog[3, 1/3] + PolyLog[3, 2/5] - 
   2 PolyLog[3, 3/7] - 2 PolyLog[3, 4/7] + PolyLog[3, 3/5] + 
   2 PolyLog[3, 2/3] + 1/4 PolyLog[3, 49/64] + PolyLog[3, 4/5] + 
   PolyLog[3, 6/7] - (53 Zeta[3])/12, 
 PolyLog[3, 5/8] -> 
  1/12 Pi^2 Log[2] + (23 Log[2]^3)/6 - 2/3 Pi^2 Log[3] - 
   2 Log[2]^2 Log[3] - 5 Log[2] Log[3]^2 + (4 Log[3]^3)/3 + 
   1/3 Pi^2 Log[5] - 7/2 Log[2]^2 Log[5] + 2 Log[2] Log[3] Log[5] +
    Log[3]^2 Log[5] + 3 Log[2] Log[5]^2 - (7 Log[5]^3)/6 + 
   2 PolyLog[3, 1/6] + 5/2 PolyLog[3, 1/5] - 6 PolyLog[3, 1/3] + 
   3 PolyLog[3, 2/5] - 6 PolyLog[3, 2/3] + 3/2 PolyLog[3, 4/5] + 
   2 PolyLog[3, 5/6] + (21 Zeta[3])/8, 
 PolyLog[3, 16/25] -> 
  4/3 Pi^2 Log[2] - (8 Log[2]^3)/3 - 4/3 Pi^2 Log[3] - 
   8 Log[2]^2 Log[3] - 16 Log[2] Log[3]^2 + (8 Log[3]^3)/3 + 
   2/3 Pi^2 Log[5] + 4 Log[2]^2 Log[5] + 8 Log[2] Log[3] Log[5] + 
   4 Log[3]^2 Log[5] + 4 Log[2] Log[5]^2 - (10 Log[5]^3)/3 + 
   8 PolyLog[3, 1/6] + 8 PolyLog[3, 1/5] - 16 PolyLog[3, 1/3] + 
   16 PolyLog[3, 2/5] - 16 PolyLog[3, 2/3] + 4 PolyLog[3, 4/5] + 
   8 PolyLog[3, 5/6] - 6 Zeta[3], 
 PolyLog[3, 9/14] -> -(11/6) Pi^2 Log[2] + (14 Log[2]^3)/3 + 
   4/3 Pi^2 Log[3] - Log[2]^2 Log[3] + 4 Log[2] Log[3]^2 - 
   2 Log[3]^3 - 1/3 Pi^2 Log[5] + 2 Log[2] Log[3] Log[5] - 
   Log[2] Log[5]^2 - Log[3] Log[5]^2 + (2 Log[5]^3)/3 + 
   1/3 Pi^2 Log[7] - 4 Log[2]^2 Log[7] - 4 Log[2] Log[3] Log[7] + 
   3 Log[2] Log[7]^2 + Log[3] Log[7]^2 - (2 Log[7]^3)/3 + 
   1/2 PolyLog[3, 9/49] - PolyLog[3, 2/7] + 4 PolyLog[3, 1/3] - 
   2 PolyLog[3, 2/5] - 2 PolyLog[3, 3/7] + 2 PolyLog[3, 4/7] - 
   2 PolyLog[3, 3/5] + 8 PolyLog[3, 2/3] + 2 PolyLog[3, 6/7] - 
   PolyLog[3, 7/8] - (83 Zeta[3])/12, 
 PolyLog[3, 15/22] -> -(5/12) Pi^2 Log[2] + (17 Log[2]^3)/6 + 
   5/2 Log[2]^2 Log[3] + Log[2] Log[3]^2 + Log[3]^3/3 + 
   5/6 Pi^2 Log[5] - Log[2]^2 Log[5] - Log[2] Log[3] Log[5] + 
   3/2 Log[3] Log[5]^2 - (2 Log[5]^3)/3 - 5/6 Pi^2 Log[7] + 
   3/2 Log[2]^2 Log[7] - Log[2] Log[3] Log[7] + Log[3]^2 Log[7] + 
   2 Log[2] Log[5] Log[7] - 2 Log[3] Log[5] Log[7] + 
   1/2 Log[5]^2 Log[7] - Log[2] Log[7]^2 + 1/2 Log[3] Log[7]^2 - 
   Log[5] Log[7]^2 + (7 Log[7]^3)/6 - 2 Log[2]^2 Log[11] + 
   Log[2] Log[3] Log[11] - Log[3]^2 Log[11] + Log[3] Log[5] Log[11] + 
   Log[5] Log[7] Log[11] - Log[7]^2 Log[11] - Log[2] Log[11]^2 - 
   Log[3] Log[11]^2 - Log[5] Log[11]^2 + Log[11]^3 - 
   PolyLog[3, 1/12] - PolyLog[3, 1/11] + PolyLog[3, 1/6] - 
   PolyLog[3, 2/11] + 1/4 PolyLog[3, 9/49] - PolyLog[3, 3/14] - 
   PolyLog[3, 4/15] - PolyLog[3, 3/11] - PolyLog[3, 2/7] - 
   PolyLog[3, 4/11] + PolyLog[3, 2/5] - 2 PolyLog[3, 3/7] - 
   PolyLog[3, 5/11] - PolyLog[3, 10/21] - PolyLog[3, 11/21] - 
   PolyLog[3, 4/7] + 2 PolyLog[3, 3/5] + 2 PolyLog[3, 2/3] + 
   PolyLog[3, 7/10] - PolyLog[3, 5/7] - PolyLog[3, 11/14] + 
   PolyLog[3, 4/5] - PolyLog[3, 11/12] + (163 Zeta[3])/24, 
 PolyLog[3, 11/16] -> 
  8 Log[2]^3 + 4/3 Pi^2 Log[3] - 4 Log[2]^2 Log[3] - 2 Log[3]^3 - 
   2/3 Pi^2 Log[5] - 4 Log[2] Log[3] Log[5] + 2 Log[3]^2 Log[5] - 
   4 Log[2] Log[5]^2 + 2 Log[3] Log[5]^2 + (4 Log[5]^3)/3 - 
   4 Log[2]^2 Log[11] + 4 Log[2] Log[3] Log[11] + 
   4 Log[2] Log[5] Log[11] - 2 Log[3] Log[5] Log[11] - 
   Log[5]^2 Log[11] - PolyLog[3, 1/11] - 2 PolyLog[3, 1/5] - 
   2 PolyLog[3, 4/15] + 2 PolyLog[3, 3/11] + 6 PolyLog[3, 1/3] + 
   8 PolyLog[3, 2/3] - 2 PolyLog[3, 11/15] - 2 PolyLog[3, 4/5] - 
   PolyLog[3, 9/11] + 2 PolyLog[3, 11/12] - (20 Zeta[3])/3, 
 PolyLog[3, 18/25] -> 
  13/12 Pi^2 Log[2] + (11 Log[2]^3)/6 - 5 Log[2]^2 Log[3] - 
   4 Log[2] Log[3]^2 - Pi^2 Log[5] + 6 Log[2]^2 Log[5] + 
   4 Log[2] Log[3] Log[5] + 2 Log[3]^2 Log[5] - 3 Log[2] Log[5]^2 - 
   3 Log[3] Log[5]^2 + 2 Log[5]^3 + 1/3 Pi^2 Log[7] - 
   Log[2]^2 Log[7] + 2 Log[2] Log[3] Log[7] - 
   2 Log[2] Log[5] Log[7] + 2 Log[3] Log[5] Log[7] - Log[5]^2 Log[7] -
    Log[3] Log[7]^2 + Log[7]^3/3 - PolyLog[3, 1/8] - 
   1/2 PolyLog[3, 9/49] - 2 PolyLog[3, 1/5] - 2 PolyLog[3, 1/3] + 
   2 PolyLog[3, 5/12] + 2 PolyLog[3, 3/7] + 2 PolyLog[3, 3/5] - 
   2 PolyLog[3, 2/3] - 2 PolyLog[3, 7/10] - 2 PolyLog[3, 4/5] + 
   2 PolyLog[3, 5/6] + (25 Zeta[3])/8, 
 PolyLog[3, 13/18] -> -(7/12) Pi^2 Log[2] - (65 Log[2]^3)/6 - 
   2 Pi^2 Log[3] + 8 Log[2]^2 Log[3] - 3 Log[2] Log[3]^2 + 
   4 Log[3]^3 + 3 Log[2] Log[5]^2 + Pi^2 Log[13] - 
   1/2 Log[2]^2 Log[13] - 6 Log[2] Log[3] Log[13] - 
   2 Log[3]^2 Log[13] - 2 Log[2] Log[5] Log[13] - 
   2 Log[5]^2 Log[13] + 4 Log[2] Log[13]^2 + 2 Log[3] Log[13]^2 + 
   2 Log[5] Log[13]^2 - (3 Log[13]^3)/2 + 2 PolyLog[3, 1/6] + 
   PolyLog[3, 3/16] + 4 PolyLog[3, 1/5] + 2 PolyLog[3, 3/13] + 
   1/2 PolyLog[3, 4/13] - 10 PolyLog[3, 1/3] + 2 PolyLog[3, 5/13] + 
   2 PolyLog[3, 2/5] - PolyLog[3, 13/25] + PolyLog[3, 8/13] - 
   8 PolyLog[3, 2/3] + 1/2 PolyLog[3, 9/13] + 2 PolyLog[3, 10/13] + 
   2 PolyLog[3, 4/5] + PolyLog[3, 12/13] + (13 Zeta[3])/8, 
 PolyLog[3, 3/4] -> -(2/3) Pi^2 Log[2] + (4 Log[2]^3)/3 + 
   2/3 Pi^2 Log[3] - 2 Log[2]^2 Log[3] + 2 Log[2] Log[3]^2 - 
   Log[3]^3 + 2 PolyLog[3, 1/3] + 4 PolyLog[3, 2/3] - (13 Zeta[3])/3, 
 PolyLog[3, 7/9] -> -(5/6) Pi^2 Log[2] - 3 Log[2]^3 + 
   2 Log[2] Log[3]^2 + 2/3 Pi^2 Log[7] - 2 Log[2] Log[3] Log[7] - 
   2 Log[3]^2 Log[7] + 2 Log[2] Log[7]^2 + 2 Log[3] Log[7]^2 - 
   Log[7]^3 + 2/3 PolyLog[3, 1/8] + PolyLog[3, 1/7] + 
   4 PolyLog[3, 1/3] + 2 PolyLog[3, 3/7] + PolyLog[3, 4/7] + 
   4 PolyLog[3, 2/3] + 2 PolyLog[3, 6/7] - (45 Zeta[3])/4, 
 PolyLog[3, 13/16] -> -(8/9) Pi^2 Log[2] + (160 Log[2]^3)/9 - 
   16/3 Log[2]^2 Log[3] + 2/9 Pi^2 Log[13] - 8 Log[2]^2 Log[13] + 
   4/3 Log[2] Log[3] Log[13] + 4/3 Log[2] Log[13]^2 - Log[13]^3/9 - 
   1/3 PolyLog[3, 1/13] - 2/3 PolyLog[3, 3/16] + 
   2/3 PolyLog[3, 4/13] - 1/3 PolyLog[3, 9/13] + 
   2/3 PolyLog[3, 12/13] + (2 Zeta[3])/3, 
 PolyLog[3, 21/25] -> -(1/3) Pi^2 Log[5] + (2 Log[5]^3)/3 + 
   1/3 Pi^2 Log[7] - 2 Log[5]^2 Log[7] + 2 Log[5] Log[7]^2 - (
   2 Log[7]^3)/3 + 1/2 PolyLog[3, 9/49] - 4 PolyLog[3, 3/7] + 
   4 PolyLog[3, 3/5] + 4 PolyLog[3, 5/7] - (7 Zeta[3])/2, 
 PolyLog[3, 13/15] -> -(1/3) Pi^2 Log[3] - Log[2] Log[3]^2 + (
   2 Log[3]^3)/3 - 1/3 Pi^2 Log[5] - Log[2] Log[3] Log[5] + 
   Log[3]^2 Log[5] + Log[3] Log[5]^2 + (2 Log[5]^3)/3 + 
   1/3 Pi^2 Log[13] + Log[2] Log[3] Log[13] - 
   1/2 Log[3]^2 Log[13] - Log[3] Log[5] Log[13] - 
   3/2 Log[5]^2 Log[13] + Log[5] Log[13]^2 - Log[13]^3/6 - 
   1/2 PolyLog[3, 1/13] - PolyLog[3, 2/15] + PolyLog[3, 1/5] - 
   1/2 PolyLog[3, 4/13] - PolyLog[3, 1/3] + PolyLog[3, 5/13] + 
   PolyLog[3, 2/5] - 1/2 PolyLog[3, 13/25] - PolyLog[3, 2/3] + 
   PolyLog[3, 10/13] + Zeta[3], 
 PolyLog[3, 22/25] -> -(2/3) Pi^2 Log[3] - 3 Log[2] Log[3]^2 + (
   4 Log[3]^3)/3 - 2/3 Pi^2 Log[5] - 4 Log[2] Log[3] Log[5] + 
   2 Log[3]^2 Log[5] - Log[2] Log[5]^2 + 2 Log[3] Log[5]^2 + (
   4 Log[5]^3)/3 + 2/3 Pi^2 Log[11] + 4 Log[2] Log[3] Log[11] - 
   Log[3]^2 Log[11] + 2 Log[2] Log[5] Log[11] - 
   2 Log[3] Log[5] Log[11] - 3 Log[5]^2 Log[11] - Log[2] Log[11]^2 + 
   2 Log[5] Log[11]^2 - Log[11]^3/3 - PolyLog[3, 2/11] - 
   2 PolyLog[3, 4/15] - 2 PolyLog[3, 1/3] + 2 PolyLog[3, 2/5] + 
   2 PolyLog[3, 5/11] - 2 PolyLog[3, 2/3] - PolyLog[3, 8/11] - 
   2 PolyLog[3, 11/15] + 2 PolyLog[3, 4/5] + 2 PolyLog[3, 10/11] + 
   2 Zeta[3], 
 PolyLog[3, 8/9] -> -(3/2) Pi^2 Log[2] + 2 Pi^2 Log[3] + 
   3 Log[2] Log[3]^2 - (8 Log[3]^3)/3 + 6 PolyLog[3, 1/3] + 
   18 PolyLog[3, 2/3] - (247 Zeta[3])/12, 
 PolyLog[3, 9/10] -> -(1/12) Pi^2 Log[2] - (5 Log[2]^3)/6 + 
   4/3 Pi^2 Log[3] - 4 Log[2]^2 Log[3] - 2 Log[3]^3 - 
   1/3 Pi^2 Log[5] + 5/2 Log[2]^2 Log[5] + 2 Log[3]^2 Log[5] + 
   Log[2] Log[5]^2 - (5 Log[5]^3)/6 + 2 PolyLog[3, 1/6] + 
   3/2 PolyLog[3, 1/5] + 4 PolyLog[3, 2/5] + 2 PolyLog[3, 3/5] + 
   6 PolyLog[3, 2/3] - 3/2 PolyLog[3, 4/5] + 4 PolyLog[3, 5/6] - (
   343 Zeta[3])/24, 
 PolyLog[3, 14/15] -> -(17/12) Pi^2 Log[2] - 7 Log[2]^3 + 
   1/6 Pi^2 Log[3] - Log[2]^2 Log[3] + 5/2 Log[2] Log[3]^2 - (
   4 Log[3]^3)/3 + 1/6 Pi^2 Log[5] + Log[2]^2 Log[5] - 
   Log[2] Log[3] Log[5] + 3/2 Log[2] Log[5]^2 + Log[3] Log[5]^2 - 
   Log[5]^3/3 + 2/3 Pi^2 Log[7] + 9/2 Log[2]^2 Log[7] - 
   1/2 Log[3]^2 Log[7] - 2 Log[2] Log[5] Log[7] - 
   Log[3] Log[5] Log[7] - 1/2 Log[5]^2 Log[7] + Log[3] Log[7]^2 + 
   Log[5] Log[7]^2 - (2 Log[7]^3)/3 + 1/3 PolyLog[3, 1/8] + 
   PolyLog[3, 1/7] + 4 PolyLog[3, 1/3] + PolyLog[3, 5/12] - 
   PolyLog[3, 4/7] + PolyLog[3, 3/5] + 6 PolyLog[3, 2/3] + 
   2 PolyLog[3, 5/7] + 1/4 PolyLog[3, 49/64] + 2 PolyLog[3, 4/5] - 
   2 PolyLog[3, 5/6] + 2 PolyLog[3, 6/7] - PolyLog[3, 7/8] - (
   99 Zeta[3])/8, 
 PolyLog[3, 15/16] -> -(23/6) Pi^2 Log[2] + (35 Log[2]^3)/3 + 
   4/3 Pi^2 Log[3] - 5 Log[2]^2 Log[3] + 10 Log[2] Log[3]^2 - (
   8 Log[3]^3)/3 + 4/3 Pi^2 Log[5] - 10 Log[2]^2 Log[5] - 
   2 Log[2] Log[3] Log[5] - 2 Log[3]^2 Log[5] + 4 Log[2] Log[5]^2 + 
   Log[3] Log[5]^2 - (2 Log[5]^3)/3 - 2 PolyLog[3, 1/6] - 
   PolyLog[3, 1/5] + 8 PolyLog[3, 1/3] - 2 PolyLog[3, 2/5] + 
   2 PolyLog[3, 3/5] + 14 PolyLog[3, 2/3] + 5 PolyLog[3, 4/5] - 
   4 PolyLog[3, 5/6] - (71 Zeta[3])/4, 
 PolyLog[3, 21/22] -> 
  1/6 Pi^2 Log[2] - (8 Log[2]^3)/3 + 4 Log[2]^2 Log[3] - 
   Log[2] Log[3]^2 - 2 Log[3]^3 + 3 Log[2]^2 Log[7] + 
   4 Log[2] Log[3] Log[7] + 2 Log[3]^2 Log[7] - 2 Log[2] Log[7]^2 - 
   Log[7]^3/3 - 2 Log[2]^2 Log[11] - 2 Log[2] Log[3] Log[11] + 
   Log[3]^2 Log[11] - Log[2] Log[7] Log[11] - 
   2 Log[3] Log[7] Log[11] + Log[7]^2 Log[11] + Log[2] Log[11]^2 - 
   PolyLog[3, 1/12] + 1/3 PolyLog[3, 1/8] - PolyLog[3, 2/11] + 
   PolyLog[3, 3/14] - PolyLog[3, 3/11] - PolyLog[3, 1/3] + 
   PolyLog[3, 4/11] + PolyLog[3, 7/18] + PolyLog[3, 11/18] + 
   PolyLog[3, 7/11] + 2 PolyLog[3, 11/14] + PolyLog[3, 9/11] - 
   PolyLog[3, 6/7] + PolyLog[3, 7/8] - 2 PolyLog[3, 11/12] - (
   7 Zeta[3])/4, 
 PolyLog[3, 24/25] -> 
  1/3 Pi^2 Log[2] - (2 Log[2]^3)/3 + 2/3 Pi^2 Log[3] - 
   2 Log[2]^2 Log[3] - 3 Log[2] Log[3]^2 - Log[3]^3/3 - 
   2/3 Pi^2 Log[5] + 2 Log[2]^2 Log[5] + 6 Log[2] Log[3] Log[5] + 
   2 Log[3]^2 Log[5] - 3 Log[2] Log[5]^2 - 3 Log[3] Log[5]^2 + (
   4 Log[5]^3)/3 - 2 PolyLog[3, 2/5] - 2 PolyLog[3, 3/5] - 
   2 PolyLog[3, 2/3] + 4 PolyLog[3, 4/5] + 4 PolyLog[3, 5/6] - (
   3 Zeta[3])/2, 
 PolyLog[3, 1 - I] -> 
  1/16 Pi^2 Log[2] - PolyLog[3, 1 + I] + (35 Zeta[3])/32, 
 PolyLog[3, -(-1)^(1/8)] -> (-(3/1024) - (21 I)/2048) Pi^3 + (
   5 Pi^3)/(128 Sqrt[2]) - 3/256 Sqrt[2 - Sqrt[2]] Pi^3 + 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/16])/4096 - PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) + (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 - (
   7 Zeta[3])/(64 Sqrt[2]) + 7/16 Sqrt[2 - Sqrt[2]] Zeta[3], 
 PolyLog[3, (-1)^(1/8)] -> (-(3/1024) + (35 I)/2048) Pi^3 - (
   3 Pi^3)/(64 Sqrt[2]) + 3/256 Sqrt[2 - Sqrt[2]] Pi^3 - 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/16])/4096 - PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) - (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 - (
   7 Zeta[3])/(64 Sqrt[2]) - 7/16 Sqrt[2 - Sqrt[2]] Zeta[3], 
 PolyLog[3, -(-1)^(1/6)] -> (1/36 - (35 I)/2592) Pi^3 + (
   7 Pi^3)/(144 Sqrt[3]) + PolyGamma[2, 1/12]/(576 Sqrt[3]) + 
   Zeta[3]/24 + (91 Zeta[3])/(72 Sqrt[3]), 
 PolyLog[3, (-1)^(1/6)] -> (-(1/36) + (55 I)/2592) Pi^3 - (
   7 Pi^3)/(144 Sqrt[3]) - PolyGamma[2, 1/12]/(576 Sqrt[3]) + 
   Zeta[3]/24 - (91 Zeta[3])/(72 Sqrt[3]), 
 PolyLog[3, -(-1)^(1/4)] -> (3/128 - (5 I)/256) Pi^3 + Pi^3/(
   32 Sqrt[2]) + PolyGamma[2, 1/8]/(256 Sqrt[2]) - (3 Zeta[3])/256 + (
   7 Zeta[3])/(8 Sqrt[2]), 
 PolyLog[3, -(1/2) (-1)^(1/4)] -> (I Pi^3)/64 + 
   5/48 Pi^2 Log[2] + 3/16 I Pi Log[2]^2 + (31 Log[2]^3)/96 + 
   1/4 PolyLog[3, -4 I] - PolyLog[3, 1/2 (-1)^(1/4)] + 
   1/2 PolyLog[3, 1/Sqrt[2]] - 1/2 PolyLog[3, Sqrt[2]], 
 PolyLog[3, (-1)^(1/4)] -> (-(3/128) + (7 I)/256) Pi^3 - Pi^3/(
   32 Sqrt[2]) - PolyGamma[2, 1/8]/(256 Sqrt[2]) - (3 Zeta[3])/256 - (
   7 Zeta[3])/(8 Sqrt[2]), 
 PolyLog[3, -(-1)^(1/3)] -> -((2 I Pi^3)/81) - (4 Zeta[3])/9, 
 PolyLog[3, (-1)^(1/3)] -> (5 I Pi^3)/162 + Zeta[3]/3, 
 PolyLog[3, -(-1)^(3/8)] -> (3/1024 - (55 I)/2048) Pi^3 + (
   5 Pi^3)/(256 Sqrt[2]) - 3/256 Sqrt[2 - Sqrt[2]] Pi^3 - 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 + (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/16])/4096 + PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) - (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 + (
   7 Zeta[3])/(64 Sqrt[2]) - 7/16 Sqrt[2 + Sqrt[2]] Zeta[3], 
 PolyLog[3, (-1)^(3/8)] -> (3/1024 + (65 I)/2048) Pi^3 - (
   3 Pi^3)/(256 Sqrt[2]) + 3/256 Sqrt[2 - Sqrt[2]] Pi^3 + 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 - (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/16])/4096 + PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) + (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 + (
   7 Zeta[3])/(64 Sqrt[2]) + 7/16 Sqrt[2 + Sqrt[2]] Zeta[3], 
 PolyLog[3, -(-1)^(5/8)] -> (3/1024 - (65 I)/2048) Pi^3 - (
   3 Pi^3)/(256 Sqrt[2]) + 3/256 Sqrt[2 - Sqrt[2]] Pi^3 + 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 - (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/16])/4096 + PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) + (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 + (
   7 Zeta[3])/(64 Sqrt[2]) + 7/16 Sqrt[2 + Sqrt[2]] Zeta[3], 
 PolyLog[3, (-1)^(5/8)] -> (3/1024 + (55 I)/2048) Pi^3 + (
   5 Pi^3)/(256 Sqrt[2]) - 3/256 Sqrt[2 - Sqrt[2]] Pi^3 - 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 + (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/16])/4096 + PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) - (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 + (
   7 Zeta[3])/(64 Sqrt[2]) - 7/16 Sqrt[2 + Sqrt[2]] Zeta[3], 
 PolyLog[3, -(-1)^(2/3)] -> -((5 I Pi^3)/162) + Zeta[3]/3, 
 PolyLog[3, (-1)^(2/3)] -> (2 I Pi^3)/81 - (4 Zeta[3])/9, 
 PolyLog[3, -(-1)^(3/4)] -> (-(3/128) - (7 I)/256) Pi^3 - Pi^3/(
   32 Sqrt[2]) - PolyGamma[2, 1/8]/(256 Sqrt[2]) - (3 Zeta[3])/256 - (
   7 Zeta[3])/(8 Sqrt[2]), 
 PolyLog[3, -(1/2) (-1)^(3/4)] -> -((I Pi^3)/64) - 
   1/16 Pi^2 Log[2] - 3/16 I Pi Log[2]^2 + (11 Log[2]^3)/32 + 
   1/4 PolyLog[3, 4 I] - PolyLog[3, 1/2 (-1)^(3/4)] - 
   1/2 PolyLog[3, 1/Sqrt[2]] + 1/2 PolyLog[3, Sqrt[2]], 
 PolyLog[3, (-1)^(3/4)] -> (3/128 + (5 I)/256) Pi^3 + Pi^3/(
   32 Sqrt[2]) + PolyGamma[2, 1/8]/(256 Sqrt[2]) - (3 Zeta[3])/256 + (
   7 Zeta[3])/(8 Sqrt[2]), 
 PolyLog[3, -(-1)^(5/6)] -> (-(1/36) - (55 I)/2592) Pi^3 - (
   7 Pi^3)/(144 Sqrt[3]) - PolyGamma[2, 1/12]/(576 Sqrt[3]) + 
   Zeta[3]/24 - (91 Zeta[3])/(72 Sqrt[3]), 
 PolyLog[3, (-1)^(5/6)] -> (1/36 + (35 I)/2592) Pi^3 + (
   7 Pi^3)/(144 Sqrt[3]) + PolyGamma[2, 1/12]/(576 Sqrt[3]) + 
   Zeta[3]/24 + (91 Zeta[3])/(72 Sqrt[3]), 
 PolyLog[3, -(-1)^(7/8)] -> (-(3/1024) - (35 I)/2048) Pi^3 - (
   3 Pi^3)/(64 Sqrt[2]) + 3/256 Sqrt[2 - Sqrt[2]] Pi^3 - 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/16])/4096 - PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) - (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 - (
   7 Zeta[3])/(64 Sqrt[2]) - 7/16 Sqrt[2 - Sqrt[2]] Zeta[3], 
 PolyLog[3, (-1)^(7/8)] -> (-(3/1024) + (21 I)/2048) Pi^3 + (
   5 Pi^3)/(128 Sqrt[2]) - 3/256 Sqrt[2 - Sqrt[2]] Pi^3 + 
   3/256 Sqrt[2 + Sqrt[2]] Pi^3 + (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/16])/4096 - PolyGamma[2, 1/8]/(
   2048 Sqrt[2]) + (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1024 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1024 + (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 3/16])/4096 - (3 Zeta[3])/2048 - (
   7 Zeta[3])/(64 Sqrt[2]) + 7/16 Sqrt[2 - Sqrt[2]] Zeta[3], 
 PolyLog[3, -(1/Sqrt[2])] -> -(1/48) Pi^2 Log[2] + Log[2]^3/24 - 
   PolyLog[3, 1/Sqrt[2]] + (7 Zeta[3])/32, 
 PolyLog[3, -(I/Sqrt[2])] -> -((I Pi^3)/16) - 1/16 Pi^2 Log[2] +
    Log[2]^3/32 - 1/2 PolyLog[3, 1/Sqrt[2]] + PolyLog[3, I Sqrt[2]] + 
   1/2 PolyLog[3, Sqrt[2]], 
 PolyLog[3, I/Sqrt[2]] -> (I Pi^3)/16 + 5/48 Pi^2 Log[2] + 
   Log[2]^3/96 - 1/24 Pi^2 Log[3] - 1/8 Log[2] Log[3]^2 + Log[3]^3/
   12 - 1/4 PolyLog[3, 1/3] - 1/4 PolyLog[3, 2/3] + 
   1/2 PolyLog[3, 1/Sqrt[2]] - PolyLog[3, I Sqrt[2]] - 
   1/2 PolyLog[3, Sqrt[2]] + Zeta[3]/4, 
 PolyLog[3, -Sqrt[2]] -> -(5/48) Pi^2 Log[2] + Log[2]^3/48 - 
   PolyLog[3, 1/Sqrt[2]] + (7 Zeta[3])/32, 
 PolyLog[3, -I Sqrt[2]] -> -(1/24) Pi^2 Log[3] - 
   1/8 Log[2] Log[3]^2 + Log[3]^3/12 - 1/4 PolyLog[3, 1/3] - 
   1/4 PolyLog[3, 2/3] - PolyLog[3, I Sqrt[2]] + Zeta[3]/4, 
 PolyLog[3, -(1/Sqrt[3])] -> 
  1/6 Pi^2 Log[3] - 1/8 I Pi Log[3]^2 - Log[3]^3/48 + 
   1/4 PolyLog[3, 1/3] - PolyLog[3, Sqrt[3]], 
 PolyLog[3, -(I/Sqrt[3])] -> -((I Pi^3)/8) - 1/8 I Pi Log[3]^2 +
    Log[3]^3/12 - 1/2 PolyLog[3, 1/3] + PolyLog[3, I/Sqrt[3]] + 
   2 PolyLog[3, I Sqrt[3]] + (13 Zeta[3])/24, 
 PolyLog[3, 1/Sqrt[3]] -> -(1/6) Pi^2 Log[3] + 
   1/8 I Pi Log[3]^2 + Log[3]^3/48 + PolyLog[3, Sqrt[3]], 
 PolyLog[3, -Sqrt[3]] -> 
  1/12 Pi^2 Log[3] - 1/8 I Pi Log[3]^2 - Log[3]^3/24 + 
   1/4 PolyLog[3, 1/3] - PolyLog[3, Sqrt[3]], 
 PolyLog[3, -I Sqrt[3]] -> -(1/12) Log[3]^3 + 1/2 PolyLog[3, 1/3] - 
   PolyLog[3, I Sqrt[3]] - (13 Zeta[3])/24, 
 PolyLog[3, -(1/Sqrt[5])] -> 
  1/6 Pi^2 Log[5] - 1/8 I Pi Log[5]^2 - Log[5]^3/48 + 
   1/4 PolyLog[3, 1/5] - PolyLog[3, Sqrt[5]], 
 PolyLog[3, -(I/Sqrt[5])] -> -((I Pi^3)/16) + 
   1/48 Pi^2 Log[5] - 1/16 I Pi Log[5]^2 + Log[5]^3/48 + 
   PolyLog[3, I Sqrt[5]], 
 PolyLog[3, I/Sqrt[5]] -> (I Pi^3)/16 - 1/24 Pi^2 Log[2] + 
   Log[2]^3/12 - 1/24 Pi^2 Log[3] + 1/4 Log[2]^2 Log[3] + 
   1/4 Log[2] Log[3]^2 + Log[3]^3/12 + 1/48 Pi^2 Log[5] - 
   1/8 Log[2]^2 Log[5] - 1/4 Log[2] Log[3] Log[5] - 
   1/8 Log[3]^2 Log[5] + 1/16 I Pi Log[5]^2 + Log[5]^3/48 - 
   1/4 PolyLog[3, 1/6] - 1/4 PolyLog[3, 5/6] - PolyLog[3, I Sqrt[5]] +
    Zeta[3]/4, 
 PolyLog[3, 1/Sqrt[5]] -> -(1/6) Pi^2 Log[5] + 
   1/8 I Pi Log[5]^2 + Log[5]^3/48 + PolyLog[3, Sqrt[5]], 
 PolyLog[3, -Sqrt[5]] -> 
  1/12 Pi^2 Log[5] - 1/8 I Pi Log[5]^2 - Log[5]^3/24 + 
   1/4 PolyLog[3, 1/5] - PolyLog[3, Sqrt[5]], 
 PolyLog[3, -I Sqrt[5]] -> -(1/24) Pi^2 Log[2] + Log[2]^3/12 - 
   1/24 Pi^2 Log[3] + 1/4 Log[2]^2 Log[3] + 1/4 Log[2] Log[3]^2 + 
   Log[3]^3/12 - 1/8 Log[2]^2 Log[5] - 1/4 Log[2] Log[3] Log[5] - 
   1/8 Log[3]^2 Log[5] - 1/4 PolyLog[3, 1/6] - 1/4 PolyLog[3, 5/6] - 
   PolyLog[3, I Sqrt[5]] + Zeta[3]/4, 
 PolyLog[3, -(1/Sqrt[6])] -> 
  1/6 Pi^2 Log[2] - 1/8 I Pi Log[2]^2 - Log[2]^3/48 + 
   1/6 Pi^2 Log[3] - 1/4 I Pi Log[2] Log[3] - 
   1/16 Log[2]^2 Log[3] - 1/8 I Pi Log[3]^2 - 
   1/16 Log[2] Log[3]^2 - Log[3]^3/48 + 1/4 PolyLog[3, 1/6] - 
   PolyLog[3, Sqrt[6]], 
 PolyLog[3, -(I/Sqrt[6])] -> -((I Pi^3)/16) + 
   1/48 Pi^2 Log[2] - 1/16 I Pi Log[2]^2 + Log[2]^3/48 + 
   1/48 Pi^2 Log[3] - 1/8 I Pi Log[2] Log[3] + 
   1/16 Log[2]^2 Log[3] - 1/16 I Pi Log[3]^2 + 
   1/16 Log[2] Log[3]^2 + Log[3]^3/48 + PolyLog[3, I Sqrt[6]], 
 PolyLog[3, I/Sqrt[6]] -> (I Pi^3)/16 + 1/48 Pi^2 Log[2] + 
   1/16 I Pi Log[2]^2 + Log[2]^3/48 + 1/48 Pi^2 Log[3] + 
   1/8 I Pi Log[2] Log[3] + 1/16 Log[2]^2 Log[3] + 
   1/16 I Pi Log[3]^2 + 1/16 Log[2] Log[3]^2 + Log[3]^3/48 - 
   1/24 Pi^2 Log[7] - 1/8 Log[2] Log[7]^2 - 1/8 Log[3] Log[7]^2 + 
   Log[7]^3/12 - 1/4 PolyLog[3, 1/7] - 1/4 PolyLog[3, 6/7] - 
   PolyLog[3, I Sqrt[6]] + Zeta[3]/4, 
 PolyLog[3, 1/Sqrt[6]] -> -(1/6) Pi^2 Log[2] + 
   1/8 I Pi Log[2]^2 + Log[2]^3/48 - 1/6 Pi^2 Log[3] + 
   1/4 I Pi Log[2] Log[3] + 1/16 Log[2]^2 Log[3] + 
   1/8 I Pi Log[3]^2 + 1/16 Log[2] Log[3]^2 + Log[3]^3/48 + 
   PolyLog[3, Sqrt[6]], 
 PolyLog[3, -Sqrt[6]] -> 
  1/12 Pi^2 Log[2] - 1/8 I Pi Log[2]^2 - Log[2]^3/24 + 
   1/12 Pi^2 Log[3] - 1/4 I Pi Log[2] Log[3] - 
   1/8 Log[2]^2 Log[3] - 1/8 I Pi Log[3]^2 - 1/8 Log[2] Log[3]^2 - 
   Log[3]^3/24 + 1/4 PolyLog[3, 1/6] - PolyLog[3, Sqrt[6]], 
 PolyLog[3, -I Sqrt[6]] -> -(1/24) Pi^2 Log[7] - 
   1/8 Log[2] Log[7]^2 - 1/8 Log[3] Log[7]^2 + Log[7]^3/12 - 
   1/4 PolyLog[3, 1/7] - 1/4 PolyLog[3, 6/7] - PolyLog[3, I Sqrt[6]] +
    Zeta[3]/4, 
 PolyLog[3, 1 - (-1)^(1/4)] -> (9 Pi^3)/784 - (15 Pi^3)/(
   98 Sqrt[2]) + 9/196 Sqrt[2 - Sqrt[2]] Pi^3 - 
   9/196 Sqrt[2 + Sqrt[2]] Pi^3 - (
   3 Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/16])/3136 + (
   3 PolyGamma[2, 1/8])/(1568 Sqrt[2]) - 
   3/784 Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8] + 
   3/784 Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8] - (
   3 Sqrt[2 - Sqrt[2]] PolyGamma[2, 3/16])/3136 + 
   4 PolyLog[3, 1 - (-1)^(1/8)] + 4/49 PolyLog[3, 1 + (-1)^(1/8)] - 
   PolyLog[3, 1 + (-1)^(3/4)] + 4/49 PolyLog[3, 1 - (-1)^(7/8)] + 
   4 PolyLog[3, 1 + (-1)^(7/8)] - (689 Zeta[3])/224 + (3 Zeta[3])/(
   7 Sqrt[2]) - 12/7 Sqrt[2 - Sqrt[2]] Zeta[3], 
 PolyLog[3, 1 - (-1)^(1/3)] -> -((5 I Pi^3)/162) + Zeta[3]/3, 
 PolyLog[3, 1 - (-1)^(3/8)] -> (3 Pi^3)/1600 + Pi^3/(
   80 Sqrt[2]) - 3/400 Sqrt[2 - Sqrt[2]] Pi^3 - 
   3/400 Sqrt[2 + Sqrt[2]] Pi^3 + (
   Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/16])/6400 + PolyGamma[2, 1/8]/(
   3200 Sqrt[2]) - (Sqrt[2 - Sqrt[2]] PolyGamma[2, 1/8])/1600 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 1/8])/1600 - (
   Sqrt[2 + Sqrt[2]] PolyGamma[2, 3/16])/6400 + 
   1/4 PolyLog[3, 1 + (-1)^(1/4)] - 9/25 PolyLog[3, 1 + (-1)^(3/8)] - 
   9/25 PolyLog[3, 1 - (-1)^(5/8)] - PolyLog[3, 1 + (-1)^(5/8)] + 
   1/4 PolyLog[3, 1 - (-1)^(3/4)] + (3549 Zeta[3])/3200 + (
   7 Zeta[3])/(100 Sqrt[2]) - 7/25 Sqrt[2 + Sqrt[2]] Zeta[3], 
 PolyLog[3, 1 - (-1)^(2/3)] -> 
  1/9 Pi^2 Log[3] - PolyLog[3, 1 + (-1)^(1/3)] + (13 Zeta[3])/9, 
 PolyLog[3, 1 + (-1)^(2/3)] -> (5 I Pi^3)/162 + Zeta[3]/3, 
 PolyLog[3, 1 - (-1)^(5/6)] -> (2 Pi^3)/3 + (7 Pi^3)/(
   6 Sqrt[3]) + PolyGamma[2, 1/12]/(24 Sqrt[3]) - 
   25 PolyLog[3, 1 - (-1)^(1/6)] - PolyLog[3, 1 + (-1)^(1/6)] - 
   25 PolyLog[3, 1 + (-1)^(5/6)] + (299 Zeta[3])/12 + (91 Zeta[3])/(
   3 Sqrt[3]), 
 PolyLog[3, 1 - 1/Sqrt[2]] -> -(1/12) Pi^2 Log[2] + Log[2]^3/24 + 
   1/8 Log[2]^2 Log[1 + Sqrt[2]] - PolyLog[3, 1/Sqrt[2]] - 
   1/4 PolyLog[3, 3 - 2 Sqrt[2]] + PolyLog[3, -1 + Sqrt[2]] + Zeta[3],
  PolyLog[3, -1 - Sqrt[2]] -> -(1/6) Pi^2 Log[1 + Sqrt[2]] - 
   1/6 Log[1 + Sqrt[2]]^3 + 1/4 PolyLog[3, 3 - 2 Sqrt[2]] - 
   PolyLog[3, -1 + Sqrt[2]], 
 PolyLog[3, 1 - Sqrt[2]] -> 
  1/4 PolyLog[3, 3 - 2 Sqrt[2]] - PolyLog[3, -1 + Sqrt[2]], 
 PolyLog[4, -(1/2)] -> 1/8 PolyLog[4, 1/4] - PolyLog[4, 1/2], 
 PolyLog[4, 1/9] -> (19 Pi^4)/135 + 20/9 Pi^2 Log[2]^2 - (
   38 Log[2]^4)/9 - 8/3 Pi^2 Log[2] Log[3] + 
   16/3 Log[2]^3 Log[3] + 2/3 Pi^2 Log[3]^2 - 
   4 Log[2]^2 Log[3]^2 + 8/3 Log[2] Log[3]^3 - (2 Log[3]^4)/3 - 
   2 PolyLog[4, 1/4] + 16 PolyLog[4, 1/3] - 16/3 PolyLog[4, 1/2] - 
   16 PolyLog[4, 2/3] - 4 PolyLog[4, 3/4], 
 PolyLog[4, 8/9] -> (7 Pi^4)/270 + 22/9 Pi^2 Log[2]^2 - (
   259 Log[2]^4)/36 - 10/3 Pi^2 Log[2] Log[3] + 
   38/3 Log[2]^3 Log[3] + 7/6 Pi^2 Log[3]^2 - 
   19/2 Log[2]^2 Log[3]^2 + 13/3 Log[2] Log[3]^3 - (25 Log[3]^4)/24 - 
   5/2 PolyLog[4, 1/4] - 7 PolyLog[4, 1/3] + 58/3 PolyLog[4, 1/2] - 
   2 PolyLog[4, 2/3] - 19/2 PolyLog[4, 3/4], 
 PolyLog[4, 15/16] -> (2843 Pi^4)/37530 + (2153 Pi^2 Log[2]^2)/
   1251 - (21811 Log[2]^4)/2502 + 1376/417 Pi^2 Log[2] Log[3] - 
   1306/417 Log[2]^3 Log[3] - 703/834 Pi^2 Log[3]^2 + 
   542/139 Log[2]^2 Log[3]^2 - 615/139 Log[2] Log[3]^3 + (
   4417 Log[3]^4)/3336 - 1412/417 Pi^2 Log[2] Log[5] + 
   6952/417 Log[2]^3 Log[5] - 212/417 Pi^2 Log[3] Log[5] - 
   607/139 Log[2]^2 Log[3] Log[5] + 322/139 Log[2] Log[3]^2 Log[5] + 
   58/417 Log[3]^3 Log[5] + 367/417 Pi^2 Log[5]^2 - 
   1156/139 Log[2]^2 Log[5]^2 + 183/139 Log[2] Log[3] Log[5]^2 - 
   95/139 Log[3]^2 Log[5]^2 + 883/417 Log[2] Log[5]^3 + 
   7/417 Log[3] Log[5]^3 - (457 Log[5]^4)/1668 - 
   28/139 PolyLog[4, 1/16] - 43/139 PolyLog[4, 1/10] - 
   117/139 PolyLog[4, 1/6] - 251/139 PolyLog[4, 1/5] + 
   1451/278 PolyLog[4, 1/4] + 1193/139 PolyLog[4, 1/3] - 
   73/139 PolyLog[4, 3/8] + 414/139 PolyLog[4, 2/5] + 
   130/139 PolyLog[4, 4/9] - 10306/417 PolyLog[4, 1/2] + 
   66/139 PolyLog[4, 5/9] + 352/139 PolyLog[4, 3/5] - 
   170/139 PolyLog[4, 5/8] + 849/139 PolyLog[4, 2/3] + 
   3271/278 PolyLog[4, 3/4] - 1203/139 PolyLog[4, 4/5] - 
   644/139 PolyLog[4, 5/6] - 183/139 PolyLog[4, 9/10]}];

PolyLogExpand[expr_] := expr /. polyLogRules;

gammaRules = Dispatch[{Gamma[1/6] -> (Sqrt[3/Pi] Gamma[1/3]^2)/2^(1/3), 
 Gamma[3/8] -> (2^(3/4) Sqrt[Pi] Gamma[1/8] Sin[Pi/8])/
  Gamma[1/4], 
 Gamma[4/9] -> (2 3^(1/6) Gamma[2/9] Gamma[1/3] Sin[(2 Pi)/9])/
  Gamma[1/9], 
 Gamma[1/10] -> ((1 + Sqrt[5]) Sqrt[(5 - Sqrt[5])/Pi]
    Gamma[1/5] Gamma[2/5])/(2 2^(7/10)), 
 Gamma[3/10] -> ((-1 + Sqrt[5]) Sqrt[Pi] Gamma[1/5])/(
  2^(3/5) Gamma[2/5]), 
 Gamma[1/12] -> (2^(1/4) 3^(3/8) Gamma[1/4] Gamma[1/3])/
  Sqrt[(-1 + Sqrt[3]) Pi], 
 Gamma[5/12] -> (2^(1/4) Sqrt[(-1 + Sqrt[3]) Pi] Gamma[1/4])/(
  3^(1/8) Gamma[1/3]), 
 Gamma[1/14] -> (Csc[Pi/14] Gamma[1/7] Gamma[3/7] Sin[Pi/7])/(
  2^(1/7) Sqrt[Pi]), 
 Gamma[3/14] -> (
  Cos[Pi/14] Csc[(3 Pi)/14] Gamma[2/7] Gamma[3/7])/(
  2^(3/7) Sqrt[Pi]), 
 Gamma[5/14] -> (Sqrt[Pi] Gamma[1/7] Sec[Pi/7])/(
  2^(5/7) Gamma[2/7]), 
 Gamma[2/15] -> ((5 + Sqrt[5])^(1/4) Gamma[1/15] Gamma[2/5] Sqrt[
   Sec[Pi/15]])/(2^(3/4) 3^(7/20) 5^(1/12) Gamma[1/3]), 
 Gamma[4/15] -> (Gamma[1/15] Gamma[2/5] Sec[(7 Pi)/30])/(
  2 3^(3/10) Gamma[1/5]), 
 Gamma[7/15] -> (
  3^(9/20) 5^(1/12) (2 (5 + Sqrt[5]))^(1/4)
    Gamma[1/5] Gamma[1/3] Sqrt[Sec[Pi/15]])/(
  Gamma[1/15] (-1 + Sqrt[5] + 4 Sin[Pi/30])), 
 Gamma[5/16] -> (2 2^(1/8) Gamma[3/16] Gamma[1/4] Sin[(3 Pi)/16])/
  Gamma[1/8], 
 Gamma[7/16] -> (Sqrt[Pi] Gamma[1/16] Sec[Pi/16])/(
  2^(7/8) Gamma[1/8]), 
 Gamma[1/18] -> (
  2^(8/9) 3^(1/6)
    Csc[Pi/18] Gamma[2/9] Gamma[1/3] Sin[Pi/9] Sin[(2 Pi)/
    9])/Sqrt[Pi], 
 Gamma[5/18] -> (
  2^(4/9) Sqrt[Pi] Csc[Pi/9] Gamma[1/9] Sin[Pi/18])/(
  3^(1/6) Gamma[1/3]), 
 Gamma[7/18] -> (Sqrt[Pi] Gamma[1/9] Sec[Pi/9])/(
  2^(7/9) Gamma[2/9]), 
 Gamma[3/20] -> (
  2^(9/20) Gamma[1/
    20] Sqrt[Pi Csc[(3 Pi)/20] Sin[Pi/
     20]])/((5 (1 + Sqrt[5]))^(1/4) Gamma[2/5]), 
 Gamma[7/20] -> ((5 + Sqrt[5])^(1/4)
    Gamma[1/20] Sec[(3 Pi)/
    20] Sqrt[(Pi Csc[(3 Pi)/20] Sin[Pi/20])/(5 - Sqrt[5])])/(
  2^(13/20) 5^(1/8) Gamma[1/5]), 
 Gamma[9/20] -> (
  2^(4/5) Sqrt[1 + 1/Sqrt[5]] Pi Gamma[1/20] Sin[Pi/20])/(
  Gamma[1/5] Gamma[2/5]), 
 Gamma[4/21] -> (
  3^(1/28) 7^(1/12) Sqrt[1 + (-1)^(2/21)/(1 + (-1)^(4/21))]
    Gamma[2/21] Gamma[1/7])/Gamma[1/21], 
 Gamma[5/21] -> (Csc[(5 Pi)/21] Gamma[2/21] Gamma[3/7])/(
  2 3^(3/14) Gamma[2/7]), 
 Gamma[8/21] -> (2 3^(5/14) Gamma[1/7] Gamma[2/7] Sin[Pi/7])/(
  Gamma[1/21] - 2 Gamma[1/21] Sin[Pi/14]), 
 Gamma[10/21] -> (
  2 3^(3/28) 7^(1/12) Gamma[2/21] Gamma[3/7] Sqrt[
   Csc[Pi/21] Sin[(2 Pi)/21] Sin[Pi/7] Sin[(4 Pi)/21]])/
  Gamma[1/21], 
 Gamma[1/22] -> (
  Csc[Pi/22] Gamma[1/11] Gamma[5/11] Sin[Pi/11])/(
  2^(1/11) Sqrt[Pi]), 
 Gamma[3/22] -> (
  Cos[(5 Pi)/22] Csc[(3 Pi)/22] Gamma[3/11] Gamma[4/11])/(
  2^(3/11) Sqrt[Pi]), 
 Gamma[5/22] -> (
  Cos[Pi/22] Csc[(5 Pi)/22] Gamma[3/11] Gamma[5/11])/(
  2^(5/11) Sqrt[Pi]), 
 Gamma[7/22] -> (Sqrt[Pi] Gamma[2/11] Sec[(2 Pi)/11])/(
  2^(7/11) Gamma[4/11]), 
 Gamma[9/22] -> (Sqrt[Pi] Gamma[1/11] Sec[Pi/11])/(
  2^(9/11) Gamma[2/11]), 
 Gamma[5/24] -> (
  2^(1/12) Gamma[1/24] Sqrt[
   1/3 Pi Csc[(5 Pi)/24] Sin[Pi/24]])/Gamma[1/3], 
 Gamma[7/24] -> (2^(3/4) Sqrt[Pi] Gamma[1/24])/(
  3^(3/8) (1 + Sqrt[2] + Sqrt[3]) Gamma[1/4]), 
 Gamma[11/24] -> (
  2^(1/3) Pi Gamma[1/24] Sec[Pi/8] Sqrt[
   Sin[Pi/24] Sin[(5 Pi)/24]])/(3^(3/8) Gamma[1/4] Gamma[1/3]), 
 Gamma[11/25] -> (
  4 5^(3/10)
    Cos[(7 Pi)/50] Gamma[4/25] Gamma[1/5] Gamma[9/25] Sin[(
    4 Pi)/25])/(Gamma[1/25] Gamma[6/25]), 
 Gamma[12/25] -> (
  4 5^(1/10)
    Cos[(9 Pi)/50] Gamma[3/25] Gamma[8/25] Gamma[2/5] Sin[(
    3 Pi)/25])/(Gamma[2/25] Gamma[7/25]), 
 Gamma[1/26] -> (
  Csc[Pi/26] Gamma[1/13] Gamma[6/13] Sin[Pi/13])/(
  2^(1/13) Sqrt[Pi]), 
 Gamma[3/26] -> (
  Csc[(3 Pi)/26] Gamma[3/13] Gamma[5/13] Sin[(3 Pi)/13])/(
  2^(3/13) Sqrt[Pi]), 
 Gamma[5/26] -> (
  Cos[(3 Pi)/26] Csc[(5 Pi)/26] Gamma[4/13] Gamma[5/13])/(
  2^(5/13) Sqrt[Pi]), 
 Gamma[7/26] -> (Sqrt[Pi] Gamma[3/13] Sec[(3 Pi)/13])/(
  2^(7/13) Gamma[6/13]), 
 Gamma[9/26] -> (Sqrt[Pi] Gamma[2/13] Sec[(2 Pi)/13])/(
  2^(9/13) Gamma[4/13]), 
 Gamma[11/26] -> (Sqrt[Pi] Gamma[1/13] Sec[Pi/13])/(
  2^(11/13) Gamma[2/13]), 
 Gamma[10/27] -> (
  2 3^(7/18) Cos[(11 Pi)/54] Gamma[1/9] Gamma[8/27])/Gamma[1/27], 
 Gamma[11/27] -> (
  2 3^(5/18) Cos[(13 Pi)/54] Gamma[2/9] Gamma[7/27])/Gamma[2/27], 
 Gamma[13/27] -> (
  4 3^(2/9) Gamma[5/27] Gamma[2/9] Gamma[1/3] Sin[(5 Pi)/27] Sin[(
    2 Pi)/9])/(Gamma[1/9] Gamma[4/27]), 
 Gamma[5/28] -> (
  7^(1/8) Gamma[3/28] Gamma[1/7] Gamma[1/4] Sqrt[
   Csc[Pi/28] Csc[(5 Pi)/28] Sec[(3 Pi)/14] Sin[(3 Pi)/
     28] Sin[Pi/7]])/(2^(1/14) Gamma[1/28] Gamma[2/7]), 
 Gamma[9/28] -> (
  7^(1/8) Gamma[3/28] Gamma[1/4] Sec[(5 Pi)/28] Sqrt[
   Cos[(3 Pi)/14] Csc[Pi/28] Csc[Pi/7] Csc[(5 Pi)/
     28] Sin[(3 Pi)/28]])/(2 Gamma[1/28]), 
 Gamma[11/28] -> (
  2^(9/14) Pi Gamma[3/28] Sec[Pi/14] Sin[(3 Pi)/28])/(
  Gamma[2/7] Gamma[3/7]), 
 Gamma[13/28] -> (
  2^(3/14) Pi Csc[Pi/7] Gamma[1/28] Sin[Pi/28])/(
  Gamma[1/7] Gamma[3/7]), 
 Gamma[1/30] -> (
  3^(9/20) 5^(1/12)
    Gamma[1/5] Gamma[1/
    3] Sqrt[((5 + Sqrt[5]) Csc[Pi/30] Csc[(2 Pi)/15] Csc[(
     7 Pi)/30] Sin[Pi/15])/Pi])/(
  2 2^(19/60) (5 - Sqrt[5])^(1/4)), 
 Gamma[7/30] -> (
  3^(3/20) 5^(1/12) Sqrt[((5 - Sqrt[5]) Cos[Pi/15])/Pi]
    Gamma[1/3] Gamma[2/5])/(2^(13/60) (5 + Sqrt[5])^(1/4)), 
 Gamma[11/30] -> (
  2 2^(1/60) (5 - Sqrt[5])^(1/4)
    Gamma[1/
    5] Sqrt[Pi Csc[Pi/15] Sin[Pi/30] Sin[(2 Pi)/15] Sin[(
     7 Pi)/30]])/(3^(1/20) 5^(1/12) Gamma[1/3]), 
 Gamma[13/30] -> (
  3^(7/20) 5^(1/12) Gamma[1/3] Sqrt[Pi Sec[Pi/15]])/(
  2^(7/60) (5 + Sqrt[5])^(1/4) Gamma[2/5]), 
 Gamma[9/32] -> (2 2^(5/16) Gamma[1/8] Gamma[7/32] Sin[(7 Pi)/32])/
  Gamma[1/16], 
 Gamma[11/32] -> (
  2 2^(11/16) Sqrt[Pi]
    Gamma[1/8] Gamma[5/32] Sin[Pi/8] Sin[(5 Pi)/32])/(
  Gamma[3/16] Gamma[1/4]), 
 Gamma[13/32] -> (Sqrt[Pi] Gamma[3/32] Sec[(3 Pi)/32])/(
  2^(13/16) Gamma[3/16]), 
 Gamma[15/32] -> (Sqrt[Pi] Gamma[1/32] Sec[Pi/32])/(
  2^(15/16) Gamma[1/16]), 
 Gamma[7/33] -> (Csc[(7 Pi)/33] Gamma[4/33] Gamma[5/11])/(
  2 3^(3/22) Gamma[4/11]), 
 Gamma[8/33] -> (
  Gamma[1/33] Gamma[4/33] Gamma[2/11] Gamma[5/11] Sqrt[
   2 Cos[Pi/22] Csc[(2 Pi)/33] Csc[(5 Pi)/33] Csc[(8 Pi)/
     33] Sin[Pi/33] Sin[(4 Pi)/33] Sin[(2 Pi)/11]])/(
  3^(5/11) 11^(1/12) Gamma[2/33] Gamma[5/33] Gamma[1/3]), 
 Gamma[10/33] -> (Gamma[1/33] Gamma[4/11] Sec[(13 Pi)/66])/(
  2 3^(9/22) Gamma[1/11]), 
 Gamma[13/33] -> (
  2 3^(7/22) Gamma[2/11] Gamma[3/11] Sin[(2 Pi)/11])/(
  Gamma[2/33] - 2 Gamma[2/33] Sin[Pi/22]), 
 Gamma[14/33] -> (
  2 Gamma[1/33] Gamma[4/33] Gamma[2/11] Gamma[3/11] Gamma[5/11] Sqrt[
   2 Cos[Pi/22] Csc[(2 Pi)/33] Csc[(5 Pi)/33] Sin[Pi/
     33] Sin[(4 Pi)/33] Sin[(2 Pi)/11] Sin[(8 Pi)/33]])/(
  3^(5/22) 11^(1/12) Gamma[2/33] Gamma[1/11] Gamma[5/33] Gamma[1/3]), 
 Gamma[16/33] -> (2 3^(1/22) Cos[Pi/22] Gamma[2/11] Gamma[5/11])/(
  Gamma[5/33] + 2 Gamma[5/33] Sin[(3 Pi)/22]), 
 Gamma[1/34] -> (
  Csc[Pi/34] Gamma[1/17] Gamma[8/17] Sin[Pi/17])/(
  2^(1/17) Sqrt[Pi]), 
 Gamma[3/34] -> (
  Csc[(3 Pi)/34] Gamma[3/17] Gamma[7/17] Sin[(3 Pi)/17])/(
  2^(3/17) Sqrt[Pi]), 
 Gamma[5/34] -> (
  Cos[(7 Pi)/34] Csc[(5 Pi)/34] Gamma[5/17] Gamma[6/17])/(
  2^(5/17) Sqrt[Pi]), 
 Gamma[7/34] -> (
  Cos[(3 Pi)/34] Csc[(7 Pi)/34] Gamma[5/17] Gamma[7/17])/(
  2^(7/17) Sqrt[Pi]), 
 Gamma[9/34] -> (Sqrt[Pi] Gamma[4/17] Sec[(4 Pi)/17])/(
  2^(9/17) Gamma[8/17]), 
 Gamma[11/34] -> (Sqrt[Pi] Gamma[3/17] Sec[(3 Pi)/17])/(
  2^(11/17) Gamma[6/17]), 
 Gamma[13/34] -> (Sqrt[Pi] Gamma[2/17] Sec[(2 Pi)/17])/(
  2^(13/17) Gamma[4/17]), 
 Gamma[15/34] -> (Sqrt[Pi] Gamma[1/17] Sec[Pi/17])/(
  2^(15/17) Gamma[2/17]), 
 Gamma[9/35] -> (
  Gamma[1/35] Gamma[3/35] Gamma[8/35] Gamma[2/7] Sqrt[
   Cos[(3 Pi)/14] Csc[(2 Pi)/35] Csc[(4 Pi)/35] Sec[(
     17 Pi)/70] Sin[Pi/35] Sin[(3 Pi)/35] Sin[(8 Pi)/
     35]])/(5^(3/28) 7^(1/10) (5/8 - Sqrt[5]/8)^(1/4)
    Gamma[2/35] Gamma[4/35] Gamma[1/5]), 
 Gamma[12/35] -> (
  7^(1/10) Csc[(4 Pi)/35] Csc[(6 Pi)/35] Gamma[1/35] Gamma[3/
    35]^2 Gamma[8/35]^2 Gamma[2/7] Gamma[2/5] Sec[(13 Pi)/70] Sin[(
    3 Pi)/35] Sin[(8 Pi)/35])/(
  2 5^(3/7) Gamma[2/35] Gamma[4/35] Gamma[1/7] Gamma[6/35] Gamma[1/
    5] Gamma[11/35]), 
 Gamma[13/35] -> (
  Csc[(6 Pi)/35] Gamma[1/35] Gamma[8/35] Gamma[3/7] Sec[(9 Pi)/
    70])/(4 5^(5/14) Gamma[1/7] Gamma[6/35]), 
 Gamma[16/35] -> (
  7^(1/5) (5/8 - Sqrt[5]/8)^(1/4)
    Csc[(6 Pi)/35] Gamma[3/35] Gamma[8/35] Gamma[2/7] Gamma[2/
    5] Sec[(3 Pi)/70] Sec[(13 Pi)/70] Sqrt[
   Cos[(3 Pi)/14] Csc[Pi/35] Csc[(2 Pi)/35] Csc[(4 Pi)/
     35] Sec[(17 Pi)/70] Sin[(3 Pi)/35] Sin[(8 Pi)/35]])/(
  8 5^(3/28) Gamma[2/35] Gamma[6/35] Gamma[11/35]), 
 Gamma[17/35] -> (
  4 5^(1/14)
    Cos[(13 Pi)/70] Gamma[4/35] Gamma[11/35] Gamma[3/7] Sin[(
    4 Pi)/35])/(Gamma[3/35] Gamma[2/7]), 
 Gamma[7/36] -> (
  Gamma[1/36] Gamma[5/
    36] Sqrt[Pi Csc[(7 Pi)/36] Csc[(2 Pi)/9] Sin[Pi/
     36] Sin[(5 Pi)/36]])/(2^(1/3) 3^(3/8) Gamma[2/9] Gamma[1/4]), 
 Gamma[11/36] -> (
  2^(5/6) Gamma[1/36] Gamma[5/
    36] Sqrt[Pi Csc[(2 Pi)/9] Sin[Pi/36] Sin[(5 Pi)/
     36] Sin[(7 Pi)/36]])/(3^(3/8) Gamma[1/9] Gamma[1/4]), 
 Gamma[13/36] -> (
  2 2^(5/6) 3^(1/6)
    Gamma[5/36] Gamma[1/3] Sin[(5 Pi)/36] Sin[(2 Pi)/9])/
  Gamma[1/9], 
 Gamma[17/36] -> (Pi Csc[Pi/9] Csc[(2 Pi)/9] Gamma[1/
    36] Sin[Pi/36])/(2^(5/6) 3^(1/6) Gamma[2/9] Gamma[1/3]), 
 Gamma[1/38] -> (
  Csc[Pi/38] Gamma[1/19] Gamma[9/19] Sin[Pi/19])/(
  2^(1/19) Sqrt[Pi]), 
 Gamma[3/38] -> (
  Csc[(3 Pi)/38] Gamma[3/19] Gamma[8/19] Sin[(3 Pi)/19])/(
  2^(3/19) Sqrt[Pi]), 
 Gamma[5/38] -> (
  Cos[(9 Pi)/38] Csc[(5 Pi)/38] Gamma[5/19] Gamma[7/19])/(
  2^(5/19) Sqrt[Pi]), 
 Gamma[7/38] -> (
  Cos[(5 Pi)/38] Csc[(7 Pi)/38] Gamma[6/19] Gamma[7/19])/(
  2^(7/19) Sqrt[Pi]), 
 Gamma[9/38] -> (
  Cos[Pi/38] Csc[(9 Pi)/38] Gamma[5/19] Gamma[9/19])/(
  2^(9/19) Sqrt[Pi]), 
 Gamma[11/38] -> (Sqrt[Pi] Gamma[4/19] Sec[(4 Pi)/19])/(
  2^(11/19) Gamma[8/19]), 
 Gamma[13/38] -> (Sqrt[Pi] Gamma[3/19] Sec[(3 Pi)/19])/(
  2^(13/19) Gamma[6/19]), 
 Gamma[15/38] -> (Sqrt[Pi] Gamma[2/19] Sec[(2 Pi)/19])/(
  2^(15/19) Gamma[4/19]), 
 Gamma[17/38] -> (Sqrt[Pi] Gamma[1/19] Sec[Pi/19])/(
  2^(17/19) Gamma[2/19]), 
 Gamma[8/39] -> (Csc[(8 Pi)/39] Gamma[5/39] Gamma[6/13])/(
  2 3^(3/26) Gamma[5/13]), 
 Gamma[10/39] -> (
  13^(1/12) Gamma[2/39] Gamma[1/13] Gamma[5/39] Gamma[4/13] Sqrt[
   Cos[(5 Pi)/26] Csc[Pi/39] Csc[(4 Pi)/39] Csc[(7 Pi)/
     39] Sec[(19 Pi)/78] Sin[(2 Pi)/39] Sin[Pi/13] Sin[(
     5 Pi)/39]])/(3^(1/13) Gamma[1/39] Gamma[4/39] Gamma[7/39]), 
 Gamma[11/39] -> (Gamma[2/39] Gamma[5/13] Sec[(17 Pi)/78])/(
  2 3^(9/26) Gamma[2/13]), 
 Gamma[14/39] -> (2 3^(11/26) Gamma[1/13] Gamma[4/13] Sin[Pi/13])/(
  Gamma[1/39] - 2 Gamma[1/39] Sin[(3 Pi)/26]), 
 Gamma[16/39] -> (
  2 3^(5/26) 13^(1/12)
    Gamma[2/39] Gamma[5/39] Gamma[3/13] Gamma[4/13] Sqrt[
   Cos[(5 Pi)/26] Cos[(19 Pi)/78] Csc[Pi/39] Csc[(4 Pi)/
     39] Csc[(7 Pi)/39] Sin[(2 Pi)/39] Sin[Pi/13] Sin[(
     5 Pi)/39]])/(Gamma[1/39] Gamma[4/39] Gamma[7/39]), 
 Gamma[17/39] -> (
  2 3^(5/26) Cos[(5 Pi)/26] Gamma[3/13] Gamma[4/13])/(
  Gamma[4/39] + 2 Gamma[4/39] Sin[Pi/26]), 
 Gamma[19/39] -> (
  2 3^(1/26) Gamma[7/39] Gamma[6/13] Sin[(7 Pi)/39])/Gamma[2/13], 
 Gamma[9/40] -> (
  2 2^(1/20) (5 - Sqrt[5])^(1/4)
    Csc[(3 Pi)/40] Gamma[1/20] Gamma[1/8]^2 Gamma[7/
    40] Sqrt[Pi Sin[Pi/20] Sin[(3 Pi)/20]]
    Sin[(7 Pi)/40])/(
  Gamma[1/40] Gamma[3/40] Gamma[1/4] Gamma[2/5]), 
 Gamma[11/40] -> ((25 - 5 Sqrt[5])^(1/4)
    Gamma[1/8]^2 Gamma[7/40] Gamma[1/5] Sqrt[
   Csc[Pi/40] Csc[(3 Pi)/40] Sec[(9 Pi)/40] Sin[(7 Pi)/
     40] Tan[Pi/8]])/(2^(4/5) Gamma[1/40] Gamma[3/40] Gamma[1/4]), 
 Gamma[13/40] -> (
  5^(3/8) (5 - Sqrt[5])^(1/4)
    Csc[Pi/40] Csc[(9 Pi)/40] Gamma[7/40] Gamma[1/5] Sin[(
    3 Pi)/40] Sin[Pi/8]^2)/(
  Gamma[1/20] Sqrt[(5 + Sqrt[5]) Sin[Pi/20] Sin[(3 Pi)/20]]), 
 Gamma[17/40] -> (
  5^(3/8) Csc[Pi/40] Csc[(7 Pi)/40] Csc[(9 Pi)/40] Gamma[3/
    40] Gamma[2/5] Tan[(3 Pi)/40] Tan[Pi/8])/(
  8 2^(4/5) (5 - Sqrt[5])^(1/4) Gamma[1/20] Sqrt[
   Sin[Pi/20] Sin[(3 Pi)/20]]), 
 Gamma[19/40] -> (
  5^(1/4) Csc[(7 Pi)/40] Csc[(9 Pi)/40] Gamma[1/40] Sec[Pi/
    40] Sqrt[(Pi Csc[Pi/40] Csc[Pi/20] Csc[(3 Pi)/
     20] Sec[(9 Pi)/40] Sin[(3 Pi)/40] Sin[(7 Pi)/
     40] Tan[Pi/8])/(5 + Sqrt[5])])/(8 2^(9/20) Gamma[1/20]), 
 Gamma[1/42] -> 
  4 2^(19/42) 3^(3/28) 7^(1/12)
    Cos[Pi/21] Gamma[2/21] Gamma[3/7] Sin[Pi/7] Sqrt[(
   Cos[(5 Pi)/21] Csc[Pi/42] Csc[(2 Pi)/21] Sec[(3 Pi)/
     14] Sin[Pi/21] Sin[(5 Pi)/42] Sin[(4 Pi)/21])/Pi], 
 Gamma[5/42] -> (
  2 2^(16/21) 3^(1/7)
    Cos[Pi/21] Cos[Pi/14] Gamma[2/21] Gamma[1/7] Gamma[3/
    7] Sec[(3 Pi)/14] Sin[Pi/7])/(Sqrt[Pi] Gamma[1/21]), 
 Gamma[11/42] -> (
  2^(10/21) Gamma[1/21] Sec[Pi/
    14] Sqrt[Pi Csc[(2 Pi)/21] Sin[Pi/21] Sin[Pi/7] Sin[(
     4 Pi)/21]])/(3^(9/28) 7^(1/12) Gamma[2/7]), 
 Gamma[13/42] -> (
  2 2^(37/42) 7^(1/12)
    Gamma[2/
    21] Sqrt[Pi Csc[Pi/7] Csc[(5 Pi)/21] Sin[Pi/14] Sin[(
     2 Pi)/21] Sin[(5 Pi)/42] Sin[(4 Pi)/21] Sin[(3 Pi)/
     14]])/(3^(9/28) Gamma[2/7]), 
 Gamma[17/42] -> (
  Gamma[1/21] Sec[(2 Pi)/
    21] Sqrt[Pi Csc[(2 Pi)/21] Csc[Pi/7] Sin[Pi/21] Sin[(
     4 Pi)/21]])/(2^(17/21) 3^(1/28) 7^(1/12) Gamma[1/7]), 
 Gamma[19/42] -> (Sqrt[Pi] Gamma[1/21] Sec[Pi/21])/(
  2^(19/21) Gamma[2/21]), 
 Gamma[9/44] -> (
  11^(1/8) Gamma[3/44] Gamma[1/11] Gamma[7/44] Gamma[1/4] Gamma[5/
    11] Sqrt[(
   Cos[Pi/22] Csc[Pi/44] Csc[(5 Pi)/44] Csc[(2 Pi)/
     11] Csc[(9 Pi)/44] Sin[(3 Pi)/44] Sin[Pi/11] Sin[(
     7 Pi)/44])/Pi])/(
  2^(1/11) Gamma[1/44] Gamma[5/44] Gamma[2/11]), 
 Gamma[13/44] -> (
  11^(1/8) Gamma[3/44] Gamma[7/44] Gamma[1/4] Gamma[5/11] Sec[(
    9 Pi)/44])/(
  2 2^(4/11)
    Gamma[1/44] Gamma[5/
    44] Sqrt[Pi Csc[(3 Pi)/44] Csc[(7 Pi)/44] Csc[(2 Pi)/
     11] Sin[Pi/44] Sin[Pi/22] Sin[(5 Pi)/44] Sin[(9 Pi)/
     44]]), Gamma[15/44] -> (
  2^(21/22) Gamma[7/44] Gamma[4/11] Sin[(7 Pi)/44])/Gamma[2/11], 
 Gamma[17/44] -> (Pi Gamma[5/44] Sec[(5 Pi)/44] Sec[(5 Pi)/
    22])/(2 2^(7/22) Gamma[3/11] Gamma[5/11]), 
 Gamma[19/44] -> (
  2^(9/22) Pi Gamma[3/44] Sec[(5 Pi)/22] Sin[(3 Pi)/44])/(
  Gamma[3/11] Gamma[4/11]), 
 Gamma[21/44] -> (
  2^(3/22) Pi Csc[Pi/11] Gamma[1/44] Sin[Pi/44])/(
  Gamma[1/11] Gamma[5/11]), 
 Gamma[13/45] -> (
  2 Gamma[1/45] Gamma[2/45] Gamma[2/9] Gamma[11/45] Gamma[1/3] Sin[(
    2 Pi)/9] Sqrt[
   Cos[Pi/18] Csc[(4 Pi)/45] Csc[(8 Pi)/45] Sec[(19 Pi)/
     90] Sin[Pi/45] Sin[(2 Pi)/45] Sin[(11 Pi)/45]])/(
  3^(1/3) 5^(11/36) (5/8 - Sqrt[5]/8)^(1/4)
    Gamma[4/45] Gamma[1/9] Gamma[8/45] Gamma[1/5]), 
 Gamma[14/45] -> (
  Csc[(7 Pi)/45] Gamma[1/45] Gamma[2/45] Gamma[11/45] Gamma[1/
    3] Sec[(13 Pi)/90] Sec[(17 Pi)/90] Sin[(2 Pi)/9])/(
  4 3^(4/15) 5^(5/18) Gamma[1/15] Gamma[1/9] Gamma[7/45]), 
 Gamma[16/45] -> (
  3^(1/6) Csc[(7 Pi)/45] Gamma[2/45] Gamma[11/45] Gamma[1/3] Sec[(
    13 Pi)/90] Sin[(2 Pi)/9])/(
  2 5^(5/18) Gamma[1/9] Gamma[7/45]), 
 Gamma[17/45] -> (
  2 Sqrt[2 (3 + Sqrt[5])]
    Cos[(13 Pi)/90] Cos[(17 Pi)/90] Csc[(8 Pi)/45] Gamma[1/
    45] Gamma[1/15] Gamma[2/9] Gamma[11/45] Gamma[2/5] Sec[(11 Pi)/
    90] Sin[Pi/45] Sin[(11 Pi)/45])/(
  3^(1/15) 5^(7/18) Gamma[4/45] Gamma[1/9] Gamma[8/45] Gamma[1/5]), 
 Gamma[19/45] -> (
  8 Sqrt[2 (3 + Sqrt[5])]
    Cos[(13 Pi)/90] Cos[(17 Pi)/90] Gamma[1/15] Gamma[11/
    45] Gamma[2/5] Sin[Pi/45] Sin[(11 Pi)/45])/(
  3^(1/15) Gamma[4/45] Gamma[1/5]), 
 Gamma[22/45] -> (
  3^(7/30) 5^(1/12) (5/8 - Sqrt[5]/8)^(1/4)
    Csc[(7 Pi)/45] Gamma[8/45] Gamma[1/5] Gamma[1/3] Sec[Pi/
    90] Sec[(13 Pi)/90] Sec[(17 Pi)/90] Sqrt[
   Cos[Pi/18] Csc[Pi/45] Csc[(2 Pi)/45] Csc[(4 Pi)/
     45] Csc[(11 Pi)/45] Sec[(19 Pi)/90] Sin[(8 Pi)/45]]
    Sin[(2 Pi)/9])/(16 Gamma[1/15] Gamma[7/45]), 
 Gamma[1/46] -> (
  Csc[Pi/46] Gamma[1/23] Gamma[11/23] Sin[Pi/23])/(
  2^(1/23) Sqrt[Pi]), 
 Gamma[3/46] -> (
  Csc[(3 Pi)/46] Gamma[3/23] Gamma[10/23] Sin[(3 Pi)/23])/(
  2^(3/23) Sqrt[Pi]), 
 Gamma[5/46] -> (
  Csc[(5 Pi)/46] Gamma[5/23] Gamma[9/23] Sin[(5 Pi)/23])/(
  2^(5/23) Sqrt[Pi]), 
 Gamma[7/46] -> (
  Cos[(9 Pi)/46] Csc[(7 Pi)/46] Gamma[7/23] Gamma[8/23])/(
  2^(7/23) Sqrt[Pi]), 
 Gamma[9/46] -> (
  Cos[(5 Pi)/46] Csc[(9 Pi)/46] Gamma[7/23] Gamma[9/23])/(
  2^(9/23) Sqrt[Pi]), 
 Gamma[11/46] -> (
  Cos[Pi/46] Csc[(11 Pi)/46] Gamma[6/23] Gamma[11/23])/(
  2^(11/23) Sqrt[Pi]), 
 Gamma[13/46] -> (Sqrt[Pi] Gamma[5/23] Sec[(5 Pi)/23])/(
  2^(13/23) Gamma[10/23]), 
 Gamma[15/46] -> (Sqrt[Pi] Gamma[4/23] Sec[(4 Pi)/23])/(
  2^(15/23) Gamma[8/23]), 
 Gamma[17/46] -> (Sqrt[Pi] Gamma[3/23] Sec[(3 Pi)/23])/(
  2^(17/23) Gamma[6/23]), 
 Gamma[19/46] -> (Sqrt[Pi] Gamma[2/23] Sec[(2 Pi)/23])/(
  2^(19/23) Gamma[4/23]), 
 Gamma[21/46] -> (Sqrt[Pi] Gamma[1/23] Sec[Pi/23])/(
  2^(21/23) Gamma[2/23]), 
 Gamma[11/48] -> (
  Sqrt[Pi]
    Gamma[1/16] Gamma[5/48] Sec[Pi/8] Sin[(5 Pi)/48])/(
  3^(3/16) Gamma[3/16] Gamma[1/4]), 
 Gamma[13/48] -> (
  2^(5/24) 3^(1/4)
    Gamma[1/16]^2 Gamma[5/48] Gamma[1/3] Sin[(5 Pi)/48] Sqrt[
   Csc[Pi/48] Csc[(7 Pi)/48] Sec[(3 Pi)/16] Sin[Pi/
     16] Tan[(11 Pi)/48]])/(Gamma[1/48] Gamma[1/8] Gamma[7/48]), 
 Gamma[17/48] -> (
  3^(7/16) Cos[Pi/8] Csc[Pi/48] Gamma[1/16] Gamma[3/16] Gamma[1/
    4] Sec[(7 Pi)/48] Sec[(3 Pi)/16] Sin[Pi/16])/(
  2^(7/8) Gamma[1/48] Gamma[1/8]), 
 Gamma[19/48] -> (
  2 2^(5/24) 3^(9/16)
    Gamma[1/16] Gamma[5/48] Gamma[3/16] Gamma[1/3] Sin[(5 Pi)/
    48] Sqrt[
   Cos[(11 Pi)/48] Csc[Pi/48] Csc[(7 Pi)/48] Sec[(3 Pi)/
     16] Sin[Pi/16] Sin[(11 Pi)/48]])/(
  Gamma[1/48] Gamma[1/8] Gamma[7/48]), 
 Gamma[23/48] -> (
  2^(1/8) 3^(1/16) Sqrt[Pi] Gamma[1/16] Gamma[3/16])/(
  Gamma[1/8] Gamma[7/48] + 2 Gamma[1/8] Gamma[7/48] Sin[Pi/8]), 
 Gamma[1/50] -> (
  5^(1/10) Sqrt[5 - Sqrt[5]]
    Csc[Pi/50] Csc[(4 Pi)/25] Csc[(9 Pi)/50] Csc[(6 Pi)/
    25] Gamma[1/25] Gamma[3/25] Gamma[8/25] Gamma[2/5] Sin[(3 Pi)/
    50])/(8 2^(27/50) Sqrt[Pi] Gamma[2/25] Gamma[7/25]), 
 Gamma[3/50] -> (
  5^(3/10) Cos[(9 Pi)/50] Cos[(11 Pi)/50] Csc[(3 Pi)/
    50] Csc[(7 Pi)/50] Gamma[3/25] Gamma[4/25] Gamma[1/5] Gamma[9/
    25] Sec[(4 Pi)/25] Sin[(3 Pi)/25])/(
  2^(3/25) Sqrt[Pi] Gamma[1/25] Gamma[6/25]), 
 Gamma[7/50] -> (
  Cos[(11 Pi)/50] Csc[(7 Pi)/50] Gamma[7/25] Gamma[9/25])/(
  2^(7/25) Sqrt[Pi]), 
 Gamma[9/50] -> (
  Cos[(7 Pi)/50] Csc[(9 Pi)/50] Gamma[8/25] Gamma[9/25])/(
  2^(9/25) Sqrt[Pi]), 
 Gamma[11/50] -> (
  2 2^(14/25) 5^(3/10)
    Cos[(3 Pi)/50] Cos[(7 Pi)/50] Csc[(11 Pi)/50] Gamma[4/
    25] Gamma[1/5] Gamma[7/25] Gamma[9/25] Sin[(4 Pi)/25])/(
  Sqrt[Pi] Gamma[1/25] Gamma[6/25]), 
 Gamma[13/50] -> (
  Sqrt[Pi]
    Csc[(3 Pi)/25] Gamma[2/25] Gamma[6/25] Gamma[7/25] Sec[(
    9 Pi)/50] Sec[(6 Pi)/25])/(
  4 2^(13/25) 5^(1/10) Gamma[3/25] Gamma[8/25] Gamma[2/5]), 
 Gamma[17/50] -> (Sqrt[Pi] Gamma[4/25] Sec[(4 Pi)/25])/(
  2^(17/25) Gamma[8/25]), 
 Gamma[19/50] -> (Sqrt[Pi] Gamma[3/25] Sec[(3 Pi)/25])/(
  2^(19/25) Gamma[6/25]), 
 Gamma[21/50] -> (Sqrt[Pi] Gamma[2/25] Sec[(2 Pi)/25])/(
  2^(21/25) Gamma[4/25]), 
 Gamma[23/50] -> (Sqrt[Pi] Gamma[1/25] Sec[Pi/25])/(
  2^(23/25) Gamma[2/25]), 
 Gamma[10/51] -> (Csc[(10 Pi)/51] Gamma[7/51] Gamma[8/17])/(
  2 3^(3/34) Gamma[7/17]), 
 Gamma[13/51] -> (Gamma[4/51] Gamma[7/17] Sec[(25 Pi)/102])/(
  2 3^(9/34) Gamma[4/17]), 
 Gamma[14/51] -> (
  Gamma[1/51] Gamma[4/51] Gamma[2/17] Gamma[7/51] Gamma[5/17] Gamma[8/
    17] Sqrt[
   2 Cos[Pi/34] Cos[(7 Pi)/34] Csc[(2 Pi)/51] Csc[(5 Pi)/
     51] Csc[(8 Pi)/51] Csc[(11 Pi)/51] Sec[(23 Pi)/
     102] Sin[Pi/51] Sin[(4 Pi)/51] Sin[(2 Pi)/17] Sin[(
     7 Pi)/51]])/(
  3^(39/68) 17^(1/12)
    Gamma[2/51] Gamma[5/51] Gamma[8/51] Gamma[11/51] Gamma[1/3]), 
 Gamma[16/51] -> (Gamma[1/51] Gamma[6/17] Sec[(19 Pi)/102])/(
  2 3^(15/34) Gamma[1/17]), 
 Gamma[19/51] -> (
  3^(13/34) Csc[(2 Pi)/51] Gamma[2/17] Gamma[5/17] Sec[(13 Pi)/
    102] Sin[(2 Pi)/17])/(2 Gamma[2/51]), 
 Gamma[20/51] -> (
  2 Gamma[1/51] Gamma[4/51] Gamma[2/17] Gamma[7/51] Gamma[3/17] Gamma[
    5/17] Gamma[8/17] Sqrt[
   2 Cos[Pi/34] Cos[(7 Pi)/34] Cos[(23 Pi)/102] Csc[(
     2 Pi)/51] Csc[(5 Pi)/51] Csc[(8 Pi)/51] Csc[(11 Pi)/
     51] Sin[Pi/51] Sin[(4 Pi)/51] Sin[(2 Pi)/17] Sin[(
     7 Pi)/51]])/(
  3^(1/4) 17^(1/12)
    Gamma[2/51] Gamma[1/17] Gamma[5/51] Gamma[8/51] Gamma[11/
    51] Gamma[1/3]), 
 Gamma[22/51] -> (
  3^(7/34) Cos[(7 Pi)/34] Csc[(5 Pi)/51] Gamma[4/17] Gamma[5/
    17] Sec[(7 Pi)/102])/(2 Gamma[5/51]), 
 Gamma[23/51] -> (
  2 3^(5/34) Gamma[11/51] Gamma[6/17] Sin[(11 Pi)/51])/Gamma[2/17],
  Gamma[25/51] -> (2 3^(1/34) Cos[Pi/34] Gamma[3/17] Gamma[8/17])/(
  Gamma[8/51] (1 + 2 Sin[(5 Pi)/34])), 
 Gamma[11/52] -> (
  Gamma[1/52] Gamma[5/52] Gamma[9/52] Gamma[3/
    13] Sqrt[Pi Csc[(3 Pi)/52] Csc[(7 Pi)/52] Csc[(2 Pi)/
     13] Csc[(11 Pi)/52] Sec[Pi/26] Sin[Pi/52] Sin[(5 Pi)/
     52] Sin[(9 Pi)/52] Sin[(3 Pi)/13]])/(
  2^(9/26) 13^(1/8) Gamma[3/52] Gamma[7/52] Gamma[2/13] Gamma[6/13]), 
 Gamma[15/52] -> (
  Csc[Pi/13] Gamma[1/52] Gamma[5/52] Gamma[9/52] Gamma[3/13] Sec[(
    11 Pi)/
    52] Sqrt[Pi Csc[(3 Pi)/52] Csc[(7 Pi)/52] Csc[(11 Pi)/
     52] Sec[Pi/26] Sin[Pi/52] Sin[(5 Pi)/52] Sin[(2 Pi)/
     13] Sin[(9 Pi)/52] Sin[(3 Pi)/13]])/(
  2 2^(1/13) 13^(1/8)
    Gamma[3/52] Gamma[1/13] Gamma[7/52] Gamma[6/13]), 
 Gamma[17/52] -> (
  2 2^(1/26) Gamma[9/52] Gamma[4/13] Sin[(9 Pi)/52])/Gamma[2/13], 
 Gamma[19/52] -> (
  2^(21/26) Gamma[7/52] Gamma[6/13] Sin[(7 Pi)/52])/Gamma[3/13], 
 Gamma[21/52] -> (
  2^(15/26) Pi Gamma[5/52] Sec[(3 Pi)/26] Sin[(5 Pi)/52])/(
  Gamma[4/13] Gamma[5/13]), 
 Gamma[23/52] -> (
  2^(9/26) Pi Csc[(3 Pi)/13] Gamma[3/52] Sin[(3 Pi)/52])/(
  Gamma[3/13] Gamma[5/13]), 
 Gamma[25/52] -> (
  2^(3/26) Pi Csc[Pi/13] Gamma[1/52] Sin[Pi/52])/(
  Gamma[1/13] Gamma[6/13]), 
 Gamma[1/54] -> (
  3^(2/9) Csc[Pi/54] Gamma[1/27] Gamma[5/27] Gamma[2/9] Gamma[1/
    3] Sec[(5 Pi)/27] Sec[(11 Pi)/54] Sin[Pi/9] Sin[(
    2 Pi)/9])/(2 2^(1/27) Sqrt[Pi] Gamma[1/9] Gamma[4/27]), 
 Gamma[5/54] -> (
  3^(5/18) Gamma[5/27] Gamma[2/9] Gamma[7/
    27] (1 + 2 Sin[(11 Pi)/54]))/(
  2^(5/27) Sqrt[Pi] (-1 + 2 Cos[(4 Pi)/27]) Gamma[2/27]), 
 Gamma[7/54] -> (
  3^(7/18) Cos[(5 Pi)/54] Cos[(13 Pi)/54] Csc[(7 Pi)/
    54] Csc[(11 Pi)/54] Gamma[1/9] Gamma[7/27] Gamma[8/27])/(
  2^(7/27) Sqrt[Pi] Gamma[1/27]), 
 Gamma[11/54] -> (
  2^(16/27) 3^(5/18)
    Cos[(5 Pi)/54] Cos[(13 Pi)/54] Csc[(11 Pi)/54] Gamma[2/
    9] Gamma[7/27] Gamma[8/27])/(Sqrt[Pi] Gamma[2/27]), 
 Gamma[13/54] -> (
  2 2^(14/27) 3^(2/9)
    Cos[Pi/54] Csc[(13 Pi)/54] Gamma[5/27] Gamma[2/9] Gamma[7/
    27] Gamma[1/3] Sin[(5 Pi)/27] Sin[(2 Pi)/9])/(
  Sqrt[Pi] Gamma[1/9] Gamma[4/27]), 
 Gamma[17/54] -> (Sqrt[Pi] Gamma[1/27] Gamma[5/27])/(
  2^(17/27) 3^(7/18)
    Gamma[1/9] Gamma[8/27] (Cos[Pi/54] + Sin[Pi/9])), 
 Gamma[19/54] -> (Sqrt[Pi] Gamma[4/27] Sec[(4 Pi)/27])/(
  2^(19/27) Gamma[8/27]), 
 Gamma[23/54] -> (Sqrt[Pi] Gamma[2/27] Sec[(2 Pi)/27])/(
  2^(23/27) Gamma[4/27]), 
 Gamma[25/54] -> (Sqrt[Pi] Gamma[1/27] Sec[Pi/27])/(
  2^(25/27) Gamma[2/27]), 
 Gamma[17/55] -> (
  5^(7/44) 11^(1/5)
    Gamma[3/55] Gamma[4/55] Gamma[1/11] Gamma[9/55] Gamma[2/11] Gamma[
    14/55] Sqrt[
   Cos[(27 Pi)/110] Csc[Pi/55] Csc[(2 Pi)/55] Csc[(6 Pi)/
     55] Csc[(7 Pi)/55] Csc[(12 Pi)/55] Sec[(21 Pi)/
     110] Sin[(3 Pi)/55] Sin[(4 Pi)/55] Sin[Pi/11] Sin[(
     9 Pi)/55] Sin[(2 Pi)/11]])/(
  Gamma[1/55] Gamma[2/55] Gamma[6/55] Gamma[7/55] Gamma[12/55]), 
 Gamma[19/55] -> (
  Csc[(8 Pi)/55] Gamma[3/55] Gamma[14/55] Gamma[5/11] Sec[(
    17 Pi)/110])/(4 5^(5/22) Gamma[8/55] Gamma[3/11]), 
 Gamma[21/55] -> (
  11^(3/10) Cos[(27 Pi)/110] Csc[(2 Pi)/55] Csc[(7 Pi)/
    55] Csc[(8 Pi)/55] Csc[(13 Pi)/55] Gamma[3/55] Gamma[4/
    55]^2 Gamma[9/55]^2 Gamma[2/11] Gamma[14/55]^2 Gamma[5/11] Sec[(
    19 Pi)/110] Sin[(4 Pi)/55] Sin[(9 Pi)/55] Sin[(2 Pi)/
    11])/(2 5^(1/22)
    Gamma[1/55] Gamma[2/55] Gamma[6/55] Gamma[7/55] Gamma[8/55] Gamma[
    13/55] Gamma[16/55] Gamma[18/55]), 
 Gamma[23/55] -> (
  5^(4/11) 11^(3/10)
    Cos[(27 Pi)/110] Csc[Pi/55] Csc[(2 Pi)/55] Csc[(7 Pi)/
    55] Csc[(8 Pi)/55] Csc[(12 Pi)/55] Csc[(13 Pi)/55] Gamma[
    3/55] Gamma[4/55]^2 Gamma[1/11] Gamma[9/55]^2 Gamma[2/11]^2 Gamma[
    14/55]^2 Gamma[5/11] Sec[(9 Pi)/110] Sec[(19 Pi)/110] Sin[(
    4 Pi)/55] Sin[Pi/11] Sin[(9 Pi)/55] Sin[(2 Pi)/11])/(
  8 Gamma[1/55]^2 Gamma[2/55] Gamma[6/55] Gamma[7/55] Gamma[8/
    55] Gamma[12/55] Gamma[13/55] Gamma[16/55] Gamma[18/55]), 
 Gamma[24/55] -> (
  5^(7/22) Csc[(2 Pi)/55] Csc[(13 Pi)/55] Gamma[9/55] Gamma[2/
    11] Gamma[4/11] Sec[(7 Pi)/110] Sin[(2 Pi)/11])/(
  4 Gamma[2/55] Gamma[13/55]), 
 Gamma[26/55] -> (
  4 5^(3/22)
    Cos[(19 Pi)/110] Gamma[7/55] Gamma[18/55] Gamma[4/11] Sin[(
    7 Pi)/55])/(Gamma[4/55] Gamma[3/11]), 
 Gamma[27/55] -> (
  4 5^(9/44) 11^(1/5)
    Gamma[3/55] Gamma[4/55] Gamma[9/55] Gamma[2/11] Gamma[14/
    55] Gamma[5/11] Sqrt[
   Cos[(21 Pi)/110] Cos[(27 Pi)/110] Csc[Pi/55] Csc[(
     2 Pi)/55] Csc[(7 Pi)/55] Csc[(12 Pi)/55] Sin[(3 Pi)/
     55] Sin[(4 Pi)/55] Sin[Pi/11] Sin[(6 Pi)/55] Sin[(
     9 Pi)/55] Sin[(2 Pi)/11]])/(
  Gamma[1/55] Gamma[2/55] Gamma[7/55] Gamma[12/55] Gamma[16/55]), 
 Gamma[17/56] -> (
  2^(1/7) 7^(1/4)
    Gamma[5/56] Gamma[1/8]^2 Gamma[13/56] Gamma[2/7] Gamma[3/7] Sqrt[(
   Cos[Pi/14] Cos[(3 Pi)/14] Csc[Pi/56] Csc[(3 Pi)/
     56] Csc[(9 Pi)/56] Sec[(11 Pi)/56] Sin[(5 Pi)/56] Sin[(
     13 Pi)/56] Tan[Pi/8])/Pi])/(
  Gamma[1/56] Gamma[3/56] Gamma[9/56] Gamma[1/4]), 
 Gamma[19/56] -> (
  7^(1/8) Cos[Pi/14] Csc[(3 Pi)/56] Csc[(11 Pi)/56] Gamma[5/
    56] Gamma[1/8]^2 Gamma[1/7] Gamma[13/56]^2 Gamma[3/7] Sec[Pi/
    8] Sec[(9 Pi)/56] Sin[(13 Pi)/56])/(
  2 2^(2/7) Gamma[1/56] Gamma[3/56] Gamma[11/56] Gamma[1/4]^2 Gamma[
    15/56]), 
 Gamma[23/56] -> (
  2^(9/14) 7^(1/8)
    Cos[Pi/14] Csc[(3 Pi)/56] Csc[(11 Pi)/56] Gamma[5/
    56]^2 Gamma[1/8]^2 Gamma[13/56]^2 Gamma[2/7] Gamma[3/7] Sec[Pi/
    8] Sin[(5 Pi)/56] Sin[(13 Pi)/56])/(
  Gamma[1/56] Gamma[3/56] Gamma[9/56] Gamma[11/56] Gamma[1/4]^2 Gamma[
    15/56]), 
 Gamma[25/56] -> ((7/2)^(1/4)
    Csc[(11 Pi)/56] Gamma[5/56] Gamma[1/8]^2 Gamma[13/56] Sec[(
    3 Pi)/56] Sin[Pi/
    8] Sqrt[Pi Csc[Pi/56] Csc[(3 Pi)/56] Csc[(9 Pi)/
     56] Sin[(5 Pi)/56] Sin[(3 Pi)/28] Sin[(11 Pi)/56] Sin[(
     13 Pi)/56]])/(
  Gamma[1/56] Gamma[9/56] Gamma[11/56] Gamma[1/4]), 
 Gamma[27/
   56] -> (Pi Csc[(13 Pi)/56] Gamma[1/56] Gamma[15/
    56] Sec[Pi/56] Sec[Pi/14])/(
  8 2^(3/14) Gamma[1/7] Gamma[13/56] Gamma[3/7]), 
 Gamma[11/57] -> (Csc[(11 Pi)/57] Gamma[8/57] Gamma[9/19])/(
  2 3^(3/38) Gamma[8/19]), 
 Gamma[14/57] -> (Csc[(14 Pi)/57] Gamma[5/57] Gamma[8/19])/(
  2 3^(9/38) Gamma[5/19]), 
 Gamma[16/57] -> (
  19^(1/12) Gamma[2/57] Gamma[1/19] Gamma[5/57] Gamma[8/57] Gamma[4/
    19] Gamma[7/19] Sqrt[
   Cos[(5 Pi)/38] Csc[Pi/57] Csc[(4 Pi)/57] Csc[(7 Pi)/
     57] Csc[(10 Pi)/57] Csc[(13 Pi)/57] Sec[(25 Pi)/
     114] Sin[(2 Pi)/57] Sin[Pi/19] Sin[(5 Pi)/57] Sin[(
     8 Pi)/57] Sin[(4 Pi)/19]])/(
  3^(15/76) Gamma[1/57] Gamma[4/57] Gamma[7/57] Gamma[10/57] Gamma[13/
    57]), Gamma[17/57] -> (
  Gamma[2/57] Gamma[7/19] Sec[(23 Pi)/114])/(
  2 3^(15/38) Gamma[2/19]), 
 Gamma[20/57] -> (2 3^(17/38) Gamma[1/19] Gamma[6/19] Sin[Pi/19])/(
  Gamma[1/57] - 2 Gamma[1/57] Sin[(5 Pi)/38]), 
 Gamma[22/57] -> (
  2 3^(11/76) 19^(1/12)
    Gamma[2/57] Gamma[5/57] Gamma[8/57] Gamma[3/19] Gamma[4/19] Gamma[
    7/19] Sqrt[
   Cos[(5 Pi)/38] Cos[(25 Pi)/114] Csc[Pi/57] Csc[(4 Pi)/
     57] Csc[(7 Pi)/57] Csc[(10 Pi)/57] Csc[(13 Pi)/57] Sin[(
     2 Pi)/57] Sin[Pi/19] Sin[(5 Pi)/57] Sin[(8 Pi)/
     57] Sin[(4 Pi)/19]])/(
  Gamma[1/57] Gamma[4/57] Gamma[7/57] Gamma[10/57] Gamma[13/57]), 
 Gamma[23/57] -> (
  2 3^(11/38) Gamma[4/19] Gamma[5/19] Sin[(4 Pi)/19])/(
  Gamma[4/57] - 2 Gamma[4/57] Sin[Pi/38]), 
 Gamma[25/57] -> (
  2 3^(7/38) Gamma[13/57] Gamma[6/19] Sin[(13 Pi)/57])/Gamma[2/19],
  Gamma[26/57] -> (
  2 3^(5/38) Cos[(5 Pi)/38] Gamma[4/19] Gamma[7/19])/(
  Gamma[7/57] + 2 Gamma[7/57] Sin[(3 Pi)/38]), 
 Gamma[28/57] -> (
  2 3^(1/38) Gamma[10/57] Gamma[9/19] Sin[(10 Pi)/57])/Gamma[3/19],
  Gamma[1/58] -> (
  Csc[Pi/58] Gamma[1/29] Gamma[14/29] Sin[Pi/29])/(
  2^(1/29) Sqrt[Pi]), 
 Gamma[3/58] -> (
  Csc[(3 Pi)/58] Gamma[3/29] Gamma[13/29] Sin[(3 Pi)/29])/(
  2^(3/29) Sqrt[Pi]), 
 Gamma[5/58] -> (
  Csc[(5 Pi)/58] Gamma[5/29] Gamma[12/29] Sin[(5 Pi)/29])/(
  2^(5/29) Sqrt[Pi]), 
 Gamma[7/58] -> (
  Csc[(7 Pi)/58] Gamma[7/29] Gamma[11/29] Sin[(7 Pi)/29])/(
  2^(7/29) Sqrt[Pi]), 
 Gamma[9/58] -> (
  Cos[(11 Pi)/58] Csc[(9 Pi)/58] Gamma[9/29] Gamma[10/29])/(
  2^(9/29) Sqrt[Pi]), 
 Gamma[11/58] -> (
  Cos[(7 Pi)/58] Csc[(11 Pi)/58] Gamma[9/29] Gamma[11/29])/(
  2^(11/29) Sqrt[Pi]), 
 Gamma[13/58] -> (
  Cos[(3 Pi)/58] Csc[(13 Pi)/58] Gamma[8/29] Gamma[13/29])/(
  2^(13/29) Sqrt[Pi]), 
 Gamma[15/58] -> (Sqrt[Pi] Gamma[7/29] Sec[(7 Pi)/29])/(
  2^(15/29) Gamma[14/29]), 
 Gamma[17/58] -> (Sqrt[Pi] Gamma[6/29] Sec[(6 Pi)/29])/(
  2^(17/29) Gamma[12/29]), 
 Gamma[19/58] -> (Sqrt[Pi] Gamma[5/29] Sec[(5 Pi)/29])/(
  2^(19/29) Gamma[10/29]), 
 Gamma[21/58] -> (Sqrt[Pi] Gamma[4/29] Sec[(4 Pi)/29])/(
  2^(21/29) Gamma[8/29]), 
 Gamma[23/58] -> (Sqrt[Pi] Gamma[3/29] Sec[(3 Pi)/29])/(
  2^(23/29) Gamma[6/29]), 
 Gamma[25/58] -> (Sqrt[Pi] Gamma[2/29] Sec[(2 Pi)/29])/(
  2^(25/29) Gamma[4/29]), 
 Gamma[27/58] -> (Sqrt[Pi] Gamma[1/29] Sec[Pi/29])/(
  2^(27/29) Gamma[2/29]), 
 Gamma[11/60] -> (
  2^(1/4) (3 + Sqrt[5])^(3/4)
    Cos[(7 Pi)/30] Gamma[1/60] Sin[Pi/60] Sqrt[
   1/3 Pi Cos[Pi/60] Csc[Pi/20] Csc[(2 Pi)/15] Csc[(
     11 Pi)/60] Sec[(7 Pi)/60] Sec[(13 Pi)/60] Sin[Pi/
     15] Sin[(3 Pi)/20]])/(5^(5/24) Gamma[1/3]), 
 Gamma[13/60] -> (
  5^(1/8) (5 + Sqrt[5])^(1/4)
    Gamma[7/60] Sqrt[(Pi Csc[Pi/20] Sin[(3 Pi)/20])/(
   5 - Sqrt[5])])/(
  2^(11/20) 3^(3/20) (Cos[Pi/20] + Cos[(11 Pi)/60]) Gamma[2/5]),
  Gamma[17/60] -> (
  2 2^(3/4) 5^(1/24) (3 - Sqrt[5])^(1/4)
    Csc[(2 Pi)/15] Gamma[7/60] Sin[(7 Pi)/60] Sqrt[
   1/3 Pi Csc[Pi/20] Sin[Pi/30] Sin[(3 Pi)/20]]
    Sin[(13 Pi)/60])/Gamma[1/3], 
 Gamma[19/60] -> (
  2 2^(7/20)
    Gamma[1/60] Sin[Pi/
    60] Sqrt[(5 + Sqrt[5]) Pi Cos[Pi/60] Csc[Pi/20] Sec[(
     7 Pi)/60] Sec[(13 Pi)/60] Sin[(3 Pi)/20] Sin[(11 Pi)/
     60]])/(3^(9/20) 5^(1/8) (5 - Sqrt[5])^(3/4) Gamma[1/5]), 
 Gamma[23/60] -> (
  2 2^(9/20) (5 - Sqrt[5])^(
   1/4) Pi Csc[Pi/15] Gamma[7/60] Sin[(7 Pi)/60])/(
  3^(3/20) 5^(1/12) Sqrt[(5 + Sqrt[5]) Csc[Pi/30]]
    Gamma[1/3] Gamma[2/5]), 
 Gamma[29/60] -> -((
   2 2^(17/20) (5 + Sqrt[5])^(
    3/4) Pi Cos[(7 Pi)/30] Gamma[1/60] Sqrt[Sec[Pi/15]]
     Sin[Pi/60])/(
   3^(9/20) 5^(1/12) (-5 + Sqrt[5]) Gamma[1/5] Gamma[1/3])), 
 Gamma[1/62] -> (
  Csc[Pi/62] Gamma[1/31] Gamma[15/31] Sin[Pi/31])/(
  2^(1/31) Sqrt[Pi]), 
 Gamma[3/62] -> (
  Csc[(3 Pi)/62] Gamma[3/31] Gamma[14/31] Sin[(3 Pi)/31])/(
  2^(3/31) Sqrt[Pi]), 
 Gamma[5/62] -> (
  Csc[(5 Pi)/62] Gamma[5/31] Gamma[13/31] Sin[(5 Pi)/31])/(
  2^(5/31) Sqrt[Pi]), 
 Gamma[7/62] -> (
  Csc[(7 Pi)/62] Gamma[7/31] Gamma[12/31] Sin[(7 Pi)/31])/(
  2^(7/31) Sqrt[Pi]), 
 Gamma[9/62] -> (
  Cos[(13 Pi)/62] Csc[(9 Pi)/62] Gamma[9/31] Gamma[11/31])/(
  2^(9/31) Sqrt[Pi]), 
 Gamma[11/62] -> (
  Cos[(9 Pi)/62] Csc[(11 Pi)/62] Gamma[10/31] Gamma[11/31])/(
  2^(11/31) Sqrt[Pi]), 
 Gamma[13/62] -> (
  Cos[(5 Pi)/62] Csc[(13 Pi)/62] Gamma[9/31] Gamma[13/31])/(
  2^(13/31) Sqrt[Pi]), 
 Gamma[15/62] -> (
  Cos[Pi/62] Csc[(15 Pi)/62] Gamma[8/31] Gamma[15/31])/(
  2^(15/31) Sqrt[Pi]), 
 Gamma[17/62] -> (Sqrt[Pi] Gamma[7/31] Sec[(7 Pi)/31])/(
  2^(17/31) Gamma[14/31]), 
 Gamma[19/62] -> (Sqrt[Pi] Gamma[6/31] Sec[(6 Pi)/31])/(
  2^(19/31) Gamma[12/31]), 
 Gamma[21/62] -> (Sqrt[Pi] Gamma[5/31] Sec[(5 Pi)/31])/(
  2^(21/31) Gamma[10/31]), 
 Gamma[23/62] -> (Sqrt[Pi] Gamma[4/31] Sec[(4 Pi)/31])/(
  2^(23/31) Gamma[8/31]), 
 Gamma[25/62] -> (Sqrt[Pi] Gamma[3/31] Sec[(3 Pi)/31])/(
  2^(25/31) Gamma[6/31]), 
 Gamma[27/62] -> (Sqrt[Pi] Gamma[2/31] Sec[(2 Pi)/31])/(
  2^(27/31) Gamma[4/31]), 
 Gamma[29/62] -> (Sqrt[Pi] Gamma[1/31] Sec[Pi/31])/(
  2^(29/31) Gamma[2/31]), 
 Gamma[20/63] -> (
  2 Gamma[1/63] Gamma[5/63] Gamma[10/63] Gamma[2/9]^2 Gamma[19/
    63] Gamma[1/3] Sqrt[
   Cos[Pi/18] Cos[(25 Pi)/126] Csc[(2 Pi)/63] Csc[(4 Pi)/
     63] Csc[(11 Pi)/63] Csc[(13 Pi)/63] Sec[Pi/14] Sec[(
     23 Pi)/126] Sin[Pi/63] Sin[(5 Pi)/63] Sin[(10 Pi)/
     63]] Sin[(2 Pi)/9]^(3/2))/(
  3^(1/84) 7^(1/36)
    Gamma[2/63] Gamma[4/63] Gamma[1/9] Gamma[11/63] Gamma[13/
    63] Gamma[3/7]), 
 Gamma[23/63] -> (
  2 3^(11/21)
    Cos[(25 Pi)/126] Csc[(8 Pi)/63] Gamma[1/63] Gamma[5/
    63] Gamma[10/63] Gamma[2/9] Gamma[2/7] Gamma[19/63]^2 Gamma[1/
    3] Sec[(29 Pi)/126] Sin[(5 Pi)/63] Sin[(2 Pi)/9])/(
  7^(7/18) Gamma[2/63] Gamma[1/9]^2 Gamma[8/63] Gamma[16/63] Gamma[17/
    63] Gamma[3/7]), 
 Gamma[25/63] -> (
  8 3^(19/21)
    Csc[Pi/18] Csc[(4 Pi)/63] Csc[(8 Pi)/63] Csc[(13 Pi)/
    63] Gamma[1/63] Gamma[5/63]^2 Gamma[1/7] Gamma[10/63]^2 Gamma[2/
    9]^3 Gamma[2/7] Gamma[19/63]^2 Gamma[1/3]^2 Sin[Pi/14] Sin[(
    5 Pi)/63] Sin[Pi/9] Sin[(19 Pi)/126] Sin[(10 Pi)/
    63] Sin[(2 Pi)/9]^2)/(
  7^(1/3) Gamma[2/63] Gamma[4/63]^2 Gamma[1/9]^3 Gamma[8/63] Gamma[11/
    63] Gamma[13/63] Gamma[16/63] Gamma[22/63] Gamma[3/7]^2), 
 Gamma[26/63] -> (
  3^(1/6) Csc[(8 Pi)/63] Gamma[1/63] Gamma[10/63] Gamma[2/9] Gamma[
    19/63] Gamma[1/3] Sec[(11 Pi)/126] Sec[(29 Pi)/126] Sin[(
    2 Pi)/9])/(4 7^(7/18) Gamma[1/9]^2 Gamma[8/63] Gamma[17/63]), 
 Gamma[29/63] -> (
  3^(11/12) Csc[(8 Pi)/63] Gamma[5/63] Gamma[1/7] Gamma[10/
    63] Gamma[2/9]^2 Gamma[2/7] Gamma[19/63] Gamma[1/3] Sec[(5 Pi)/
    126] Sec[(19 Pi)/126] Sin[Pi/7] Sqrt[
   Cos[Pi/18] Cos[(25 Pi)/126] Csc[Pi/63] Csc[(2 Pi)/
     63] Csc[(4 Pi)/63] Csc[(11 Pi)/63] Csc[(13 Pi)/
     63] Sec[Pi/14] Sec[(23 Pi)/126] Sin[(5 Pi)/63] Sin[(
     10 Pi)/63]] Sin[(2 Pi)/9]^(3/2))/(
  4 7^(1/36)
    Gamma[2/63] Gamma[4/63] Gamma[1/9] Gamma[8/63] Gamma[11/63] Gamma[
    22/63] Gamma[3/7]), 
 Gamma[31/63] -> (
  3^(29/42) Cos[Pi/18] Cos[(25 Pi)/126] Csc[(4 Pi)/63] Csc[(
    8 Pi)/63] Csc[(13 Pi)/63] Gamma[1/63] Gamma[5/63]^2 Gamma[
    10/63] Gamma[2/9]^3 Gamma[2/7] Gamma[19/63]^2 Gamma[1/
    3]^2 Sec[Pi/126] Sec[(19 Pi)/126] Sec[(29 Pi)/126] Sin[(
    5 Pi)/63] Sin[(2 Pi)/9]^2)/(
  2 7^(1/3) Gamma[2/63] Gamma[4/63] Gamma[1/9]^3 Gamma[8/63] Gamma[13/
    63] Gamma[16/63] Gamma[17/63] Gamma[22/63] Gamma[3/7]), 
 Gamma[21/65] -> (
  2^(3/4) 5^(1/26) 13^(1/10)
    Gamma[2/65] Gamma[4/65] Gamma[1/13] Gamma[7/65] Gamma[12/
    65] Gamma[3/13] Gamma[17/65] Gamma[6/13] Sqrt[
   Cos[Pi/26] Cos[(31 Pi)/130] Csc[Pi/65] Csc[(3 Pi)/
     65] Csc[(6 Pi)/65] Csc[(8 Pi)/65] Csc[(11 Pi)/65] Csc[(
     16 Pi)/65] Sec[(23 Pi)/130] Sin[(2 Pi)/65] Sin[(
     4 Pi)/65] Sin[Pi/13] Sin[(7 Pi)/65] Sin[(12 Pi)/
     65] Sin[(3 Pi)/13]])/((5 + Sqrt[5])^(1/4)
    Gamma[1/65] Gamma[3/65] Gamma[6/65] Gamma[8/65] Gamma[11/
    65] Gamma[16/65] Gamma[2/5]), 
 Gamma[22/65] -> (
  Csc[(9 Pi)/65] Gamma[4/65] Gamma[17/65] Gamma[6/13] Sec[(
    21 Pi)/130])/(4 5^(5/26) Gamma[9/65] Gamma[4/13]), 
 Gamma[24/65] -> (
  Cos[Pi/26] Cos[(31 Pi)/130] Csc[Pi/65] Csc[(6 Pi)/
    65] Csc[(9 Pi)/65] Csc[(11 Pi)/65] Csc[(14 Pi)/65] Gamma[
    2/65]^2 Gamma[4/65] Gamma[1/13] Gamma[7/65]^2 Gamma[12/
    65]^2 Gamma[3/13] Gamma[17/65]^2 Gamma[5/13] Gamma[6/13]^2 Sec[(
    17 Pi)/130] Sec[(27 Pi)/130] Sin[(2 Pi)/65] Sin[Pi/
    13] Sin[(7 Pi)/65] Sin[(12 Pi)/65])/(
  5^(1/13) 13^(1/10) Sqrt[2 (5 + Sqrt[5])]
    Gamma[1/65] Gamma[3/65] Gamma[6/65] Gamma[8/65] Gamma[9/65] Gamma[
    2/13] Gamma[11/65] Gamma[1/5] Gamma[14/65] Gamma[18/65] Gamma[19/
    65] Gamma[23/65] Gamma[2/5]), 
 Gamma[27/65] -> (
  5^(11/26) Csc[Pi/65] Csc[(14 Pi)/65] Gamma[1/13] Gamma[12/
    65] Gamma[5/13] Sec[(11 Pi)/130] Sin[Pi/13])/(
  4 Gamma[1/65] Gamma[14/65]), 
 Gamma[28/65] -> (
  5^(7/26) Cos[Pi/26] Cos[(31 Pi)/130] Csc[Pi/65] Csc[(
    6 Pi)/65] Csc[(9 Pi)/65] Csc[(14 Pi)/65] Gamma[2/
    65] Gamma[4/65] Gamma[1/13] Gamma[7/65]^2 Gamma[12/65]^2 Gamma[17/
    65]^2 Gamma[5/13] Gamma[6/13]^2 Sec[(27 Pi)/130] Sin[(2 Pi)/
    65] Sin[Pi/13] Sin[(7 Pi)/65] Sin[(12 Pi)/65])/(
  13^(1/10) Sqrt[5/8 + Sqrt[5]/8]
    Gamma[1/65] Gamma[3/65] Gamma[6/65] Gamma[8/65] Gamma[9/65] Gamma[
    1/5] Gamma[14/65] Gamma[18/65] Gamma[19/65] Gamma[23/65] Gamma[2/
    5]), Gamma[29/65] -> (
  5^(7/26) Csc[(3 Pi)/65] Csc[(16 Pi)/65] Gamma[2/13] Gamma[3/
    13] Gamma[23/65] Sec[(7 Pi)/130] Sin[(3 Pi)/13])/(
  4 Gamma[3/65] Gamma[16/65]), 
 Gamma[31/65] -> (
  4 2^(3/4) 5^(2/13) 13^(1/10)
    Gamma[2/65] Gamma[4/65] Gamma[7/65] Gamma[12/65] Gamma[3/
    13] Gamma[17/65] Gamma[5/13] Gamma[6/13] Sqrt[
   Cos[Pi/26] Cos[(23 Pi)/130] Cos[(31 Pi)/130] Csc[Pi/
     65] Csc[(3 Pi)/65] Csc[(6 Pi)/65] Csc[(11 Pi)/65] Csc[(
     16 Pi)/65] Sin[(2 Pi)/65] Sin[(4 Pi)/65] Sin[Pi/
     13] Sin[(7 Pi)/65] Sin[(8 Pi)/65] Sin[(12 Pi)/65] Sin[(
     3 Pi)/13]])/((5 + Sqrt[5])^(1/4)
    Gamma[1/65] Gamma[3/65] Gamma[6/65] Gamma[11/65] Gamma[16/
    65] Gamma[18/65] Gamma[2/5]), 
 Gamma[32/65] -> (
  5^(1/26) Cos[Pi/26] Csc[(6 Pi)/65] Gamma[7/65] Gamma[4/
    13] Gamma[6/13] Sec[Pi/130] Sec[(27 Pi)/130])/(
  4 Gamma[6/65] Gamma[19/65]), 
 Gamma[1/66] -> (
  3^(1/22) Gamma[1/33] Gamma[2/11] Gamma[5/
    11] (1 + 2 Sin[(13 Pi)/66]))/(
  2^(1/33) Sqrt[Pi] Gamma[5/33]), 
 Gamma[5/66] -> (
  8 2^(28/33)
    Cos[Pi/22] Cos[(2 Pi)/33] Cos[(5 Pi)/33] Gamma[1/
    33] Gamma[4/33] Gamma[2/11] Gamma[3/11] Gamma[5/11] Sec[(
    13 Pi)/66] Sqrt[(
   Cos[(7 Pi)/33] Csc[Pi/33] Csc[(5 Pi)/66] Csc[(4 Pi)/
     33] Sec[(3 Pi)/22] Sin[Pi/66] Sin[(2 Pi)/33] Sin[Pi/
     11] Sin[(7 Pi)/66] Sin[(5 Pi)/33] Sin[(13 Pi)/66] Sin[(
     8 Pi)/33])/Pi])/(
  3^(5/22) 11^(1/12) Gamma[2/33] Gamma[1/11] Gamma[1/3]), 
 Gamma[7/66] -> (
  2 2^(26/33) 3^(2/11)
    Cos[Pi/22] Cos[(2 Pi)/33] Gamma[4/33] Gamma[2/11] Gamma[3/
    11] Gamma[5/11] Sec[(3 Pi)/22] Sin[(2 Pi)/11])/(
  Sqrt[Pi] Gamma[2/33] Gamma[4/11]), 
 Gamma[13/66] -> (
  2^(20/33) Cos[(5 Pi)/22] Gamma[1/33] Gamma[2/11] Gamma[3/
    11] Gamma[4/11])/(3^(1/11) Sqrt[Pi] Gamma[2/33] Gamma[1/11]), 
 Gamma[17/66] -> (
  16 2^(16/33)
    Cos[(2 Pi)/33] Cos[(5 Pi)/33] Gamma[1/33] Gamma[4/33] Sec[(
    13 Pi)/66] Sqrt[
   1/3 Pi Cos[(7 Pi)/33] Csc[Pi/33] Csc[(4 Pi)/33] Sec[(
     3 Pi)/22] Sin[Pi/66] Sin[(2 Pi)/33] Sin[(5 Pi)/
     66] Sin[Pi/11] Sin[(7 Pi)/66] Sin[(5 Pi)/33] Sin[(
     13 Pi)/66] Sin[(8 Pi)/33]])/(
  11^(1/12) Gamma[2/33] Gamma[1/3]), 
 Gamma[19/66] -> (
  3^(1/11) 11^(1/12)
    Gamma[2/33] Gamma[1/11] Gamma[5/33] Gamma[1/3] Sec[(5 Pi)/
    22] Sin[Pi/
    11] Sqrt[Pi Csc[Pi/33] Csc[(4 Pi)/33] Csc[(2 Pi)/
     11] Sec[Pi/22] Sin[(2 Pi)/33] Sin[(5 Pi)/33] Sin[(
     8 Pi)/33]])/(
  2^(5/66) Gamma[1/33] Gamma[2/11] Gamma[3/11] Gamma[4/11]), 
 Gamma[23/66] -> (
  2 2^(10/33) 3^(9/22) Sqrt[Pi]
    Gamma[1/11] Gamma[5/33] Sin[(5 Pi)/33])/(
  Gamma[1/33] Gamma[4/11]), 
 Gamma[25/66] -> (
  3^(5/11) 11^(1/12)
    Gamma[2/33] Gamma[5/33] Gamma[1/3] Sec[(4 Pi)/
    33] Sqrt[Pi Csc[Pi/33] Csc[(4 Pi)/33] Csc[(2 Pi)/
     11] Sec[Pi/22] Sin[(2 Pi)/33] Sin[(5 Pi)/33] Sin[(
     8 Pi)/33]])/(2 2^(17/66) Gamma[1/33] Gamma[2/11] Gamma[5/11]),
  Gamma[29/66] -> (Sqrt[Pi] Gamma[2/33] Sec[(2 Pi)/33])/(
  2^(29/33) Gamma[4/33]), 
 Gamma[31/66] -> (Sqrt[Pi] Gamma[1/33] Sec[Pi/33])/(
  2^(31/33) Gamma[2/33]), 
 Gamma[15/68] -> (
  Gamma[1/68] Gamma[5/68] Gamma[9/68] Gamma[3/17] Gamma[13/68] Gamma[
    7/17] Sqrt[
   Cos[(3 Pi)/34] Csc[(3 Pi)/68] Csc[(7 Pi)/68] Csc[(
     2 Pi)/17] Csc[(11 Pi)/68] Csc[(15 Pi)/68] Sec[(5 Pi)/
     34] Sin[Pi/68] Sin[(5 Pi)/68] Sin[(9 Pi)/68] Sin[(
     3 Pi)/17] Sin[(13 Pi)/68]])/(
  2^(6/17) 17^(1/8)
    Gamma[3/68] Gamma[7/68] Gamma[2/17] Gamma[11/68] Gamma[6/17]), 
 Gamma[19/68] -> (
  Csc[Pi/17] Gamma[1/68] Gamma[5/68] Gamma[9/68] Gamma[3/17] Gamma[
    13/68] Gamma[7/17] Sec[(15 Pi)/68] Sqrt[
   Cos[(3 Pi)/34] Csc[(3 Pi)/68] Csc[(7 Pi)/68] Csc[(
     11 Pi)/68] Csc[(15 Pi)/68] Sec[(5 Pi)/34] Sin[Pi/
     68] Sin[(5 Pi)/68] Sin[(2 Pi)/17] Sin[(9 Pi)/68] Sin[(
     3 Pi)/17] Sin[(13 Pi)/68]])/(
  2 2^(1/34) 17^(1/8)
    Gamma[3/68] Gamma[1/17] Gamma[7/68] Gamma[11/68] Gamma[6/17]), 
 Gamma[21/68] -> (
  2 2^(5/34) Gamma[13/68] Gamma[4/17] Sin[(13 Pi)/68])/Gamma[2/17],
  Gamma[23/68] -> (
  2^(33/34) Gamma[11/68] Gamma[6/17] Sin[(11 Pi)/68])/Gamma[3/17], 
 Gamma[25/68] -> (
  2^(27/34) Gamma[9/68] Gamma[8/17] Sin[(9 Pi)/68])/Gamma[4/17], 
 Gamma[27/68] -> (Pi Gamma[7/68] Sec[(7 Pi)/68] Sec[(7 Pi)/
    34])/(2 2^(13/34) Gamma[5/17] Gamma[7/17]), 
 Gamma[29/68] -> (
  2^(15/34) Pi Gamma[5/68] Sec[(7 Pi)/34] Sin[(5 Pi)/68])/(
  Gamma[5/17] Gamma[6/17]), 
 Gamma[31/68] -> (
  2^(9/34) Pi Csc[(3 Pi)/17] Gamma[3/68] Sin[(3 Pi)/68])/(
  Gamma[3/17] Gamma[7/17]), 
 Gamma[33/68] -> (
  2^(3/34) Pi Csc[Pi/17] Gamma[1/68] Sin[Pi/68])/(
  Gamma[1/17] Gamma[8/17]), 
 Gamma[13/69] -> (Csc[(13 Pi)/69] Gamma[10/69] Gamma[11/23])/(
  2 3^(3/46) Gamma[10/23]), 
 Gamma[16/69] -> (Csc[(16 Pi)/69] Gamma[7/69] Gamma[10/23])/(
  2 3^(9/46) Gamma[7/23]), 
 Gamma[19/69] -> (Gamma[4/69] Gamma[9/23] Sec[(31 Pi)/138])/(
  2 3^(15/46) Gamma[4/23]), 
 Gamma[20/69] -> (
  Gamma[1/69] Gamma[4/69] Gamma[2/23] Gamma[7/69] Gamma[10/69] Gamma[
    5/23] Gamma[8/23] Gamma[11/23] Sqrt[
   2 Cos[Pi/46] Cos[(7 Pi)/46] Csc[(2 Pi)/69] Csc[(5 Pi)/
     69] Csc[(8 Pi)/69] Csc[(11 Pi)/69] Csc[(14 Pi)/69] Csc[(
     17 Pi)/69] Sec[(29 Pi)/138] Sin[Pi/69] Sin[(4 Pi)/
     69] Sin[(2 Pi)/23] Sin[(7 Pi)/69] Sin[(10 Pi)/69] Sin[(
     5 Pi)/23]])/(
  3^(16/23) 23^(1/12)
    Gamma[2/69] Gamma[5/69] Gamma[8/69] Gamma[11/69] Gamma[14/
    69] Gamma[17/69] Gamma[1/3]), 
 Gamma[22/69] -> (Gamma[1/69] Gamma[8/23] Sec[(25 Pi)/138])/(
  2 3^(21/46) Gamma[1/23]), 
 Gamma[25/69] -> (
  2 3^(19/46) Gamma[2/23] Gamma[7/23] Sin[(2 Pi)/23])/(
  Gamma[2/69] - 2 Gamma[2/69] Sin[(5 Pi)/46]), 
 Gamma[26/69] -> (
  2 Gamma[1/69] Gamma[4/69] Gamma[2/23] Gamma[7/69] Gamma[3/23] Gamma[
    10/69] Gamma[5/23] Gamma[8/23] Gamma[11/23] Sqrt[
   2 Cos[Pi/46] Cos[(7 Pi)/46] Cos[(29 Pi)/138] Csc[(
     2 Pi)/69] Csc[(5 Pi)/69] Csc[(8 Pi)/69] Csc[(11 Pi)/
     69] Csc[(14 Pi)/69] Csc[(17 Pi)/69] Sin[Pi/69] Sin[(
     4 Pi)/69] Sin[(2 Pi)/23] Sin[(7 Pi)/69] Sin[(10 Pi)/
     69] Sin[(5 Pi)/23]])/(
  3^(15/46) 23^(1/12)
    Gamma[2/69] Gamma[1/23] Gamma[5/69] Gamma[8/69] Gamma[11/
    69] Gamma[14/69] Gamma[17/69] Gamma[1/3]), 
 Gamma[28/69] -> (
  2 3^(13/46) Gamma[5/23] Gamma[6/23] Sin[(5 Pi)/23])/(
  Gamma[5/69] - 2 Gamma[5/69] Sin[Pi/46]), 
 Gamma[29/69] -> (
  2 3^(11/46) Gamma[17/69] Gamma[6/23] Sin[(17 Pi)/69])/
  Gamma[2/23], 
 Gamma[31/69] -> (
  2 3^(7/46) Cos[(7 Pi)/46] Gamma[5/23] Gamma[8/23])/(
  Gamma[8/69] + 2 Gamma[8/69] Sin[(3 Pi)/46]), 
 Gamma[32/69] -> (
  2 3^(5/46) Gamma[14/69] Gamma[9/23] Sin[(14 Pi)/69])/Gamma[3/23],
  Gamma[34/69] -> (
  2 3^(1/46) Cos[Pi/46] Gamma[4/23] Gamma[11/23])/(
  Gamma[11/69] + 2 Gamma[11/69] Sin[(7 Pi)/46]), 
 Gamma[1/70] -> (
  5^(1/14) Csc[Pi/70] Csc[(6 Pi)/35] Csc[(13 Pi)/70] Gamma[1/
    35] Gamma[4/35] Gamma[11/35] Gamma[3/7] Sec[Pi/14] Sec[(
    4 Pi)/35] Sin[Pi/7])/(
  16 2^(1/35) Sqrt[Pi] Gamma[3/35] Gamma[2/7]), 
 Gamma[3/70] -> (
  128 2^(23/140) 7^(1/5)
    Cos[(3 Pi)/70] Cos[(6 Pi)/35] Gamma[3/35]^2 Gamma[8/
    35] Gamma[2/7] Gamma[2/5] Sin[(6 Pi)/35] Sin[(13 Pi)/
    70] Sqrt[((5 - Sqrt[5]) Cos[Pi/35] Cos[(2 Pi)/35] Cos[Pi/
     14] Cos[(17 Pi)/70] Cot[(4 Pi)/35] Sin[Pi/35] Sin[(
     2 Pi)/35] Sin[(17 Pi)/70] Tan[(3 Pi)/35] Tan[(8 Pi)/
     35])/Pi])/(
  5^(3/28) (5 + Sqrt[5])^(1/4) Gamma[2/35] Gamma[6/35] Gamma[11/35]), 
 Gamma[9/70] -> (
  16 2^(69/140)
    Cos[(3 Pi)/70] Cos[(6 Pi)/35] Gamma[1/35]^2 Gamma[3/
    35] Gamma[8/35]^2 Gamma[2/7] Gamma[3/7] Sin[Pi/7] Sqrt[(
   Cos[(17 Pi)/70] Csc[(4 Pi)/35] Sec[(3 Pi)/14] Sin[Pi/
     35] Sin[(2 Pi)/35] Sin[(3 Pi)/35] Sin[(8 Pi)/
     35])/Pi])/(
  5^(13/28) 7^(1/10) (5 - Sqrt[5])^(1/4)
    Gamma[2/35] Gamma[4/35] Gamma[1/7] Gamma[6/35] Gamma[1/5]), 
 Gamma[11/70] -> (
  7^(1/10) Csc[Pi/70]^3 Csc[(3 Pi)/70] Csc[(4 Pi)/35] Csc[(
    9 Pi)/70]^2 Csc[(11 Pi)/70]^2 Csc[(13 Pi)/70] Csc[(
    17 Pi)/70]^3 Gamma[1/35] Gamma[3/35]^2 Gamma[8/35]^2 Gamma[2/
    7] Gamma[2/5] Sin[Pi/35]^4 Sin[(2 Pi)/35] Sin[(3 Pi)/
    35]^2 Sin[(3 Pi)/14] Sin[(8 Pi)/35]^2)/(
  8 2^(11/35) 5^(3/7) Sqrt[Pi]
    Gamma[2/35] Gamma[4/35] Gamma[1/7] Gamma[6/35] Gamma[1/5]), 
 Gamma[13/70] -> (
  Csc[(6 Pi)/35] Csc[(13 Pi)/70] Gamma[1/35] Gamma[8/35] Gamma[
    11/35] Gamma[3/7])/(
  4 2^(13/35) 5^(5/14) Sqrt[Pi] Gamma[1/7] Gamma[6/35]), 
 Gamma[17/70] -> (
  8 2^(37/140) (5 + Sqrt[5])^(1/4)
    Cos[(3 Pi)/70] Cos[(13 Pi)/70] Gamma[1/35] Gamma[8/
    35] Gamma[11/35] Gamma[3/7] Sin[(6 Pi)/35] Sqrt[(
   Cos[(2 Pi)/35] Cos[Pi/14] Cos[(4 Pi)/35] Cot[(17 Pi)/
     70] Csc[(3 Pi)/35] Csc[(8 Pi)/35] Sec[(3 Pi)/35] Sec[(
     8 Pi)/35] Sin[(2 Pi)/35] Sin[(4 Pi)/35] Tan[Pi/
     35])/((5 - Sqrt[5]) Pi)])/(
  5^(1/28) 7^(1/10) Gamma[2/35] Gamma[1/5]), 
 Gamma[19/70] -> (
  8 2^(29/140) 5^(3/28)
    Cos[(3 Pi)/70] Cos[(13 Pi)/70] Gamma[2/35] Gamma[6/
    35] Gamma[11/35] Sec[(8 Pi)/
    35] Sqrt[Pi Cos[(17 Pi)/70] Csc[(3 Pi)/35] Csc[(8 Pi)/
     35] Sec[(3 Pi)/14] Sin[Pi/35] Sin[(2 Pi)/35] Sin[(
     4 Pi)/35]] Sin[(6 Pi)/35])/(
  7^(1/5) (5 - Sqrt[5])^(1/4) Gamma[3/35] Gamma[2/7] Gamma[2/5]), 
 Gamma[23/70] -> (
  2^(12/35) 5^(3/7) Sqrt[Pi]
    Cos[(13 Pi)/70] Csc[(3 Pi)/35] Csc[(8 Pi)/35] Gamma[2/
    35] Gamma[4/35] Gamma[1/7] Gamma[6/35]^2 Gamma[1/5] Gamma[11/
    35] Sin[(4 Pi)/35] Tan[(6 Pi)/35])/(
  7^(1/10) Gamma[1/35] Gamma[3/35]^2 Gamma[8/35]^2 Gamma[2/7] Gamma[2/
    5]), Gamma[27/70] -> (Sqrt[Pi] Gamma[4/35] Sec[(4 Pi)/35])/(
  2^(27/35) Gamma[8/35]), 
 Gamma[29/70] -> (Sqrt[Pi] Gamma[3/35] Sec[(3 Pi)/35])/(
  2^(29/35) Gamma[6/35]), 
 Gamma[31/70] -> (Sqrt[Pi] Gamma[2/35] Sec[(2 Pi)/35])/(
  2^(31/35) Gamma[4/35]), 
 Gamma[33/70] -> (Sqrt[Pi] Gamma[1/35] Sec[Pi/35])/(
  2^(33/35) Gamma[2/35]), 
 Gamma[23/72] -> (
  Csc[(2 Pi)/9] Gamma[1/72] Gamma[1/9] Gamma[11/72] Gamma[19/
    72] Sqrt[Pi Cos[(17 Pi)/72] Csc[(5 Pi)/72] Csc[(7 Pi)/
     72] Sec[Pi/18] Sec[(13 Pi)/72] Sin[Pi/72] Sin[(
     11 Pi)/72]])/(
  2 2^(17/36) 3^(5/12) Gamma[5/72] Gamma[7/72] Gamma[2/9] Gamma[1/3]),
  Gamma[25/72] -> (
  Sqrt[Pi]
    Cos[Pi/8] Cos[(17 Pi)/72] Csc[(5 Pi)/72] Csc[(13 Pi)/
    72] Csc[(2 Pi)/9]^2 Gamma[1/72] Gamma[1/9] Gamma[11/
    72]^2 Gamma[1/4] Gamma[19/72]^2 Sin[Pi/72] Sin[(11 Pi)/
    72])/(2^(7/12) 3^(1/24)
    Gamma[5/72] Gamma[7/72] Gamma[13/72] Gamma[2/9]^2 Gamma[17/
    72] Gamma[1/3]), 
 Gamma[29/72] -> (
  Sqrt[Pi]
    Cos[Pi/8] Cos[(17 Pi)/72] Csc[(5 Pi)/72] Csc[Pi/
    9] Csc[(13 Pi)/72] Csc[(2 Pi)/9] Gamma[1/72] Gamma[11/
    72] Gamma[1/4] Gamma[19/72]^2 Sec[(7 Pi)/72] Sin[Pi/72])/(
  4 2^(19/36) 3^(1/24)
    Gamma[5/72] Gamma[13/72] Gamma[2/9] Gamma[17/72] Gamma[1/3]), 
 Gamma[31/72] -> (
  Csc[(13 Pi)/72] Csc[(2 Pi)/9] Gamma[1/72] Gamma[11/72] Gamma[
    19/72] Sec[(5 Pi)/
    72] Sqrt[Pi Cos[Pi/18] Cos[(17 Pi)/72] Csc[(5 Pi)/
     72] Csc[(7 Pi)/72] Sec[(13 Pi)/72] Sin[Pi/72] Sin[(
     11 Pi)/72]])/(
  4 2^(31/36) 3^(1/4) Gamma[7/72] Gamma[13/72] Gamma[2/9]), 
 Gamma[35/72] -> (Pi Cos[(17 Pi)/72] Csc[Pi/9] Csc[(2 Pi)/
    9] Gamma[1/72] Gamma[19/72] Sin[Pi/72])/(
  2^(5/18) 3^(1/6) Gamma[2/9] Gamma[17/72] Gamma[1/3]), 
 Gamma[1/74] -> (
  Csc[Pi/74] Gamma[1/37] Gamma[18/37] Sin[Pi/37])/(
  2^(1/37) Sqrt[Pi]), 
 Gamma[3/74] -> (
  Csc[(3 Pi)/74] Gamma[3/37] Gamma[17/37] Sin[(3 Pi)/37])/(
  2^(3/37) Sqrt[Pi]), 
 Gamma[5/74] -> (
  Csc[(5 Pi)/74] Gamma[5/37] Gamma[16/37] Sin[(5 Pi)/37])/(
  2^(5/37) Sqrt[Pi]), 
 Gamma[7/74] -> (
  Csc[(7 Pi)/74] Gamma[7/37] Gamma[15/37] Sin[(7 Pi)/37])/(
  2^(7/37) Sqrt[Pi]), 
 Gamma[9/74] -> (
  Csc[(9 Pi)/74] Gamma[9/37] Gamma[14/37] Sin[(9 Pi)/37])/(
  2^(9/37) Sqrt[Pi]), 
 Gamma[11/74] -> (
  Cos[(15 Pi)/74] Csc[(11 Pi)/74] Gamma[11/37] Gamma[13/37])/(
  2^(11/37) Sqrt[Pi]), 
 Gamma[13/74] -> (
  Cos[(11 Pi)/74] Csc[(13 Pi)/74] Gamma[12/37] Gamma[13/37])/(
  2^(13/37) Sqrt[Pi]), 
 Gamma[15/74] -> (
  Cos[(7 Pi)/74] Csc[(15 Pi)/74] Gamma[11/37] Gamma[15/37])/(
  2^(15/37) Sqrt[Pi]), 
 Gamma[17/74] -> (
  Cos[(3 Pi)/74] Csc[(17 Pi)/74] Gamma[10/37] Gamma[17/37])/(
  2^(17/37) Sqrt[Pi]), 
 Gamma[19/74] -> (Sqrt[Pi] Gamma[9/37] Sec[(9 Pi)/37])/(
  2^(19/37) Gamma[18/37]), 
 Gamma[21/74] -> (Sqrt[Pi] Gamma[8/37] Sec[(8 Pi)/37])/(
  2^(21/37) Gamma[16/37]), 
 Gamma[23/74] -> (Sqrt[Pi] Gamma[7/37] Sec[(7 Pi)/37])/(
  2^(23/37) Gamma[14/37]), 
 Gamma[25/74] -> (Sqrt[Pi] Gamma[6/37] Sec[(6 Pi)/37])/(
  2^(25/37) Gamma[12/37]), 
 Gamma[27/74] -> (Sqrt[Pi] Gamma[5/37] Sec[(5 Pi)/37])/(
  2^(27/37) Gamma[10/37]), 
 Gamma[29/74] -> (Sqrt[Pi] Gamma[4/37] Sec[(4 Pi)/37])/(
  2^(29/37) Gamma[8/37]), 
 Gamma[31/74] -> (Sqrt[Pi] Gamma[3/37] Sec[(3 Pi)/37])/(
  2^(31/37) Gamma[6/37]), 
 Gamma[33/74] -> (Sqrt[Pi] Gamma[2/37] Sec[(2 Pi)/37])/(
  2^(33/37) Gamma[4/37]), 
 Gamma[35/74] -> (Sqrt[Pi] Gamma[1/37] Sec[Pi/37])/(
  2^(35/37) Gamma[2/37]), 
 Gamma[14/75] -> (
  Csc[(4 Pi)/25] Csc[(9 Pi)/50] Csc[(14 Pi)/75] Gamma[1/
    25] Gamma[3/25] Gamma[11/75] Gamma[6/25] Gamma[8/25] Gamma[2/
    5] Sin[(3 Pi)/25])/(
  4 3^(3/50) 5^(1/5)
    Gamma[2/25] Gamma[4/25] Gamma[1/5] Gamma[7/25] Gamma[9/25]), 
 Gamma[17/75] -> (
  2 5^(3/10)
    Cos[(7 Pi)/50] Csc[(17 Pi)/75] Gamma[8/75] Gamma[4/
    25] Gamma[1/5] Gamma[9/25] Sin[(4 Pi)/25])/(
  3^(9/50) Gamma[1/25] Gamma[6/25] Gamma[8/25]), 
 Gamma[22/75] -> (
  3^(3/100) 5^(1/4)
    Gamma[2/75] Gamma[1/25] Gamma[8/75] Gamma[11/75] Gamma[4/
    25] Gamma[7/25] Gamma[1/3] Sqrt[
   1/2 Cos[(11 Pi)/50] Csc[Pi/75] Csc[(4 Pi)/75] Csc[(
     7 Pi)/75] Csc[(13 Pi)/75] Csc[(16 Pi)/75] Sec[(
     31 Pi)/150] Sec[(37 Pi)/150] Sin[(2 Pi)/75] Sin[Pi/
     25] Sin[(8 Pi)/75] Sin[(11 Pi)/75] Sin[(4 Pi)/25]])/(
  Gamma[1/75] Gamma[4/75] Gamma[7/75] Gamma[13/75] Gamma[16/75] Gamma[
    19/75]), 
 Gamma[23/75] -> (Gamma[2/75] Gamma[9/25] Sec[(29 Pi)/150])/(
  2 3^(21/50) Gamma[2/25]), 
 Gamma[26/75] -> (2 3^(23/50) Gamma[1/25] Gamma[8/25] Sin[Pi/25])/(
  Gamma[1/75] - 2 Gamma[1/75] Sin[(7 Pi)/50]), 
 Gamma[28/75] -> (
  3^(41/100) 5^(1/4)
    Gamma[2/75] Gamma[8/75] Gamma[3/25] Gamma[11/75] Gamma[4/
    25] Gamma[7/25] Gamma[1/3] Sqrt[
   2 Cos[(31 Pi)/150] Cos[(11 Pi)/50] Csc[Pi/75] Csc[(
     4 Pi)/75] Csc[(7 Pi)/75] Csc[(13 Pi)/75] Csc[(16 Pi)/
     75] Sec[(37 Pi)/150] Sin[(2 Pi)/75] Sin[Pi/25] Sin[(
     8 Pi)/75] Sin[(11 Pi)/75] Sin[(4 Pi)/25]])/(
  Gamma[1/75] Gamma[4/75] Gamma[7/75] Gamma[13/75] Gamma[16/75] Gamma[
    19/75]), 
 Gamma[29/75] -> (
  2 3^(17/50) Gamma[4/25] Gamma[7/25] Sin[(4 Pi)/25])/(
  Gamma[4/75] - 2 Gamma[4/75] Sin[(3 Pi)/50]), 
 Gamma[31/75] -> (
  2 3^(13/50) Cos[(37 Pi)/150] Gamma[6/25] Gamma[19/75])/
  Gamma[2/25], 
 Gamma[32/75] -> (
  2 3^(11/50) Cos[(11 Pi)/50] Gamma[6/25] Gamma[7/25])/(
  Gamma[7/75] + 2 Gamma[7/75] Sin[Pi/50]), 
 Gamma[34/75] -> (
  2 3^(7/50) Gamma[16/75] Gamma[9/25] Sin[(16 Pi)/75])/Gamma[3/25],
  Gamma[37/75] -> (
  8 3^(1/50) 5^(1/10)
    Cos[(9 Pi)/50] Gamma[3/25] Gamma[13/75] Gamma[8/25] Gamma[2/
    5] Sin[(3 Pi)/25] Sin[(13 Pi)/75])/(
  Gamma[2/25] Gamma[4/25] Gamma[7/25]), 
 Gamma[17/76] -> (
  19^(1/8) Gamma[3/76] Gamma[1/19] Gamma[7/76] Gamma[11/76] Gamma[15/
    76] Gamma[1/4] Gamma[5/19] Gamma[9/19] Sqrt[(
   Cos[Pi/38] Cos[(9 Pi)/38] Csc[Pi/76] Csc[(5 Pi)/
     76] Csc[(2 Pi)/19] Csc[(9 Pi)/76] Csc[(13 Pi)/76] Csc[(
     17 Pi)/76] Sec[(7 Pi)/38] Sin[(3 Pi)/76] Sin[Pi/
     19] Sin[(7 Pi)/76] Sin[(11 Pi)/76] Sin[(15 Pi)/
     76])/Pi])/(
  2^(2/19)
    Gamma[1/76] Gamma[5/76] Gamma[2/19] Gamma[9/76] Gamma[13/
    76] Gamma[6/19]), 
 Gamma[21/76] -> (
  19^(1/8) Gamma[3/76] Gamma[7/76] Gamma[11/76] Gamma[15/76] Gamma[1/
    4] Gamma[5/19] Gamma[9/19] Sec[(17 Pi)/76] Sqrt[(
   Csc[Pi/76] Csc[Pi/38] Csc[(5 Pi)/76] Csc[(9 Pi)/
     76] Csc[(13 Pi)/76] Csc[(17 Pi)/76] Sin[(3 Pi)/76] Sin[(
     7 Pi)/76] Sin[(2 Pi)/19] Sin[(5 Pi)/38] Sin[(11 Pi)/
     76] Sin[(7 Pi)/38] Sin[(15 Pi)/76])/Pi])/(
  2^(5/19) Gamma[1/76] Gamma[5/76] Gamma[9/76] Gamma[13/76] Gamma[6/
    19]), Gamma[23/76] -> (
  2 2^(7/38) Gamma[15/76] Gamma[4/19] Sin[(15 Pi)/76])/Gamma[2/19],
  Gamma[25/76] -> (
  2 2^(1/38) Gamma[13/76] Gamma[6/19] Sin[(13 Pi)/76])/Gamma[3/19],
  Gamma[27/76] -> (
  2^(33/38) Gamma[11/76] Gamma[8/19] Sin[(11 Pi)/76])/Gamma[4/19], 
 Gamma[29/76] -> (Pi Gamma[9/76] Sec[(9 Pi)/76] Sec[(9 Pi)/
    38])/(2 2^(11/38) Gamma[5/19] Gamma[9/19]), 
 Gamma[31/76] -> (
  2^(21/38) Pi Gamma[7/76] Sec[(5 Pi)/38] Sin[(7 Pi)/76])/(
  Gamma[6/19] Gamma[7/19]), 
 Gamma[33/76] -> (Pi Gamma[5/76] Sec[(5 Pi)/76] Sec[(5 Pi)/
    38])/(2 2^(23/38) Gamma[5/19] Gamma[7/19]), 
 Gamma[35/76] -> (
  2^(9/38) Pi Csc[(3 Pi)/19] Gamma[3/76] Sin[(3 Pi)/76])/(
  Gamma[3/19] Gamma[8/19]), 
 Gamma[37/76] -> (
  2^(3/38) Pi Csc[Pi/19] Gamma[1/76] Sin[Pi/76])/(
  Gamma[1/19] Gamma[9/19]), 
 Gamma[26/77] -> (7^(1/44) 11^(1/28)
      Gamma[2/77] Gamma[3/77] Gamma[6/77] Gamma[1/11] Gamma[10/
      77] Gamma[13/77] Gamma[17/77] Gamma[24/77] Gamma[4/11] Gamma[5/
      11] Sqrt[
     Cos[Pi/22] Cos[(3 Pi)/22] Cos[(29 Pi)/154] Csc[Pi/
       77] Csc[(4 Pi)/77] Csc[(5 Pi)/77] Csc[(8 Pi)/77] Csc[(
       12 Pi)/77] Csc[(15 Pi)/77] Csc[(19 Pi)/77] Sec[Pi/
       14] Sec[(25 Pi)/154] Sec[(3 Pi)/14] Sin[(2 Pi)/
       77] Sin[(3 Pi)/77] Sin[(6 Pi)/77] Sin[Pi/11] Sin[(
       10 Pi)/77] Sin[(13 Pi)/77] Sin[(17 Pi)/77]])/(Gamma[1/
      77] Gamma[4/77] Gamma[5/77] Gamma[8/77] Gamma[12/77] Gamma[15/
      77] Gamma[19/77] Gamma[2/7] Gamma[3/7]), 
 Gamma[30/77] -> (
  11^(2/7) Cos[Pi/22] Cos[(29 Pi)/154] Csc[Pi/77] Csc[(
    5 Pi)/77] Csc[(8 Pi)/77] Csc[(9 Pi)/77] Csc[(12 Pi)/
    77] Csc[(16 Pi)/77] Csc[(19 Pi)/77] Gamma[2/77] Gamma[3/
    77]^2 Gamma[6/77]^2 Gamma[1/11] Gamma[10/77]^2 Gamma[13/
    77]^2 Gamma[17/77]^2 Gamma[24/77]^2 Gamma[4/11] Gamma[5/
    11]^2 Sec[Pi/14] Sec[(17 Pi)/154] Sec[(31 Pi)/154] Sin[(
    3 Pi)/77] Sin[(6 Pi)/77] Sin[Pi/11] Sin[(10 Pi)/
    77] Sin[(13 Pi)/77] Sin[(17 Pi)/77])/(
  4 7^(1/11)
    Gamma[1/77]^2 Gamma[4/77] Gamma[5/77] Gamma[8/77]^2 Gamma[9/
    77] Gamma[12/77] Gamma[15/77] Gamma[16/77] Gamma[18/77] Gamma[19/
    77] Gamma[2/7] Gamma[23/77] Gamma[29/77] Gamma[3/7]), 
 Gamma[31/77] -> (
  Csc[(9 Pi)/77] Gamma[2/77] Gamma[13/77] Gamma[24/77] Gamma[5/
    11] Sec[(15 Pi)/154] Sec[(37 Pi)/154])/(
  8 7^(7/22) Gamma[9/77] Gamma[2/11] Gamma[20/77]), 
 Gamma[32/77] -> (
  Cos[Pi/22] Cos[(29 Pi)/154] Csc[(5 Pi)/77] Csc[(9 Pi)/
    77] Csc[(16 Pi)/77] Gamma[2/77] Gamma[3/77] Gamma[6/77] Gamma[
    10/77] Gamma[13/77] Gamma[17/77]^2 Gamma[24/77]^2 Gamma[4/
    11] Gamma[5/11]^2 Sec[Pi/14] Sec[(23 Pi)/154] Sec[(
    37 Pi)/154] Sin[(3 Pi)/77] Sin[(10 Pi)/77] Sin[(
    17 Pi)/77])/(
  2 7^(3/11) 11^(1/14)
    Gamma[4/77] Gamma[5/77] Gamma[9/77] Gamma[1/7] Gamma[2/11] Gamma[
    16/77] Gamma[18/77] Gamma[20/77] Gamma[25/77] Gamma[27/77] Gamma[
    3/7]), Gamma[34/77] -> (
  7^(3/22) Cos[Pi/22] Cos[(29 Pi)/154] Csc[Pi/77] Csc[(
    5 Pi)/77] Csc[(9 Pi)/77] Csc[(12 Pi)/77] Csc[(16 Pi)/
    77] Gamma[2/77] Gamma[3/77] Gamma[6/77] Gamma[1/11] Gamma[10/
    77]^2 Gamma[13/77] Gamma[17/77]^2 Gamma[3/11] Gamma[24/
    77]^2 Gamma[4/11] Gamma[5/11]^2 Sec[(9 Pi)/154] Sec[Pi/
    14] Sec[(23 Pi)/154] Sec[(31 Pi)/154] Sec[(37 Pi)/
    154] Sin[(3 Pi)/77] Sin[Pi/11] Sin[(10 Pi)/77] Sin[(
    17 Pi)/77])/(
  16 11^(1/14)
    Gamma[1/77] Gamma[4/77] Gamma[5/77] Gamma[9/77] Gamma[1/7] Gamma[
    12/77] Gamma[2/11] Gamma[16/77] Gamma[18/77] Gamma[20/77] Gamma[
    23/77] Gamma[25/77] Gamma[27/77] Gamma[3/7]), 
 Gamma[36/77] -> (
  2 7^(3/22) 11^(2/7)
    Cos[Pi/22] Cos[(29 Pi)/154] Csc[Pi/77] Csc[(5 Pi)/
    77] Csc[(9 Pi)/77] Csc[(12 Pi)/77] Csc[(16 Pi)/77] Gamma[
    2/77] Gamma[3/77] Gamma[6/77]^2 Gamma[1/11] Gamma[10/77]^2 Gamma[
    13/77]^2 Gamma[17/77]^2 Gamma[3/11] Gamma[24/77]^2 Gamma[4/
    11] Gamma[5/11]^2 Sec[Pi/14] Sec[(31 Pi)/154] Sin[(3 Pi)/
    77] Sin[(6 Pi)/77] Sin[Pi/11] Sin[(10 Pi)/77] Sin[(
    13 Pi)/77] Sin[(17 Pi)/77])/(
  Gamma[1/77]^2 Gamma[4/77] Gamma[5/77] Gamma[8/77] Gamma[9/77] Gamma[
    12/77] Gamma[2/11] Gamma[15/77] Gamma[16/77] Gamma[18/77] Gamma[2/
    7] Gamma[23/77] Gamma[25/77] Gamma[29/77] Gamma[3/7]), 
 Gamma[37/
   77] -> (7^(5/44)
      Gamma[1/77] Gamma[5/77] Gamma[8/77] Gamma[12/77] Gamma[18/
      77] Gamma[19/77] Gamma[2/7] Gamma[29/77] Gamma[3/7] Sec[(
      3 Pi)/154] Sqrt[
     Cos[Pi/14] Cos[(3 Pi)/22] Cos[(3 Pi)/14] Csc[(2 Pi)/
       77] Csc[(3 Pi)/77] Csc[(4 Pi)/77] Csc[(6 Pi)/
       77] Csc[Pi/11] Csc[(10 Pi)/77] Csc[(13 Pi)/77] Csc[(
       15 Pi)/77] Csc[(17 Pi)/77] Sec[Pi/22] Sec[(25 Pi)/
       154] Sec[(29 Pi)/154] Sin[Pi/77] Sin[(5 Pi)/77] Sin[(
       8 Pi)/77] Sin[(12 Pi)/77] Sin[(19 Pi)/77]])/(8 11^(
     1/28) Gamma[2/77] Gamma[3/77] Gamma[6/77] Gamma[10/77] Gamma[13/
      77] Gamma[17/77] Gamma[24/77] Gamma[5/11]), 
 Gamma[38/77] -> (
  7^(1/22) Cos[Pi/22] Csc[(5 Pi)/77] Csc[(16 Pi)/77] Gamma[6/
    77] Gamma[17/77] Gamma[4/11] Gamma[5/11] Sec[Pi/154] Sec[(
    23 Pi)/154])/(8 Gamma[5/77] Gamma[16/77] Gamma[27/77]), 
 Gamma[1/78] -> (
  2^(38/39) 3^(1/26)
    Csc[Pi/78] Gamma[1/39] Gamma[7/39] Gamma[6/13] Sin[Pi/
    39] Sin[(7 Pi)/39])/(Sqrt[Pi] Gamma[2/13]), 
 Gamma[5/78] -> (
  3^(5/26) (1 + Cos[(7 Pi)/78] Csc[(8 Pi)/39]) Gamma[5/
    39] Gamma[3/13] Gamma[4/13])/(2^(5/39) Sqrt[Pi] Gamma[4/39]), 
 Gamma[7/78] -> (
  8 2^(32/39) 3^(5/26) 13^(1/12)
    Cos[Pi/39] Cos[(4 Pi)/39] Cos[(7 Pi)/39] Csc[(8 Pi)/
    39] Gamma[2/39] Gamma[5/39] Gamma[3/13] Gamma[4/13] Sec[(
    11 Pi)/78] Sin[Pi/13] Sqrt[(
   Cos[(3 Pi)/26] Cos[(8 Pi)/39] Cos[(19 Pi)/78] Csc[Pi/
     39] Csc[(2 Pi)/39] Csc[(7 Pi)/78] Csc[(5 Pi)/39] Csc[(
     2 Pi)/13] Sin[Pi/78] Sin[(5 Pi)/78] Sin[(4 Pi)/
     39] Sin[(11 Pi)/78] Sin[(7 Pi)/39] Sin[(17 Pi)/
     78])/Pi])/(Gamma[1/39] Gamma[4/39]), 
 Gamma[11/78] -> (
  2 2^(28/39) 3^(1/13)
    Cos[Pi/39] Cos[(3 Pi)/26] Csc[(2 Pi)/13] Gamma[2/
    39] Gamma[1/13] Gamma[4/13] Gamma[5/13] Sin[Pi/13])/(
  Sqrt[Pi] Gamma[1/39] Gamma[2/13]), 
 Gamma[17/78] -> (
  2^(22/39) Gamma[2/39] Gamma[3/13] Gamma[4/13] Gamma[5/13] Sin[(
    3 Pi)/13])/(3^(2/13) Sqrt[Pi] Gamma[4/39] Gamma[2/13]), 
 Gamma[19/78] -> (
  4 2^(1/78) 13^(1/12)
    Cos[Pi/39] Cos[(4 Pi)/39] Cos[(7 Pi)/39] Csc[(8 Pi)/
    39]^(3/2)
    Gamma[2/39] Gamma[1/13] Gamma[5/39] Gamma[4/13] Gamma[6/13] Sec[(
    11 Pi)/78] Sin[Pi/13] Sin[(7 Pi)/39] Sqrt[(
   Csc[(2 Pi)/39] Csc[(3 Pi)/26] Csc[(5 Pi)/39] Csc[(
     2 Pi)/13] Csc[(19 Pi)/78] Sin[(5 Pi)/78] Sin[(4 Pi)/
     39] Sin[(11 Pi)/78] Sin[(17 Pi)/78] Sin[(3 Pi)/
     13])/Pi])/(3^(1/26) Gamma[1/39] Gamma[4/39] Gamma[2/13]), 
 Gamma[23/78] -> (
  2^(16/39) Csc[(3 Pi)/13] Gamma[1/39] Gamma[4/39] Gamma[7/
    39] Gamma[6/
    13] Sqrt[Pi Cos[(19 Pi)/78] Csc[(2 Pi)/39] Csc[(5 Pi)/
     39] Sec[(5 Pi)/26] Sin[Pi/39] Sin[Pi/13] Sin[(4 Pi)/
     39] Sin[(7 Pi)/39]])/(
  3^(4/13) 13^(1/12) Gamma[2/39] Gamma[3/13] Gamma[4/13] Gamma[5/13]),
  Gamma[25/78] -> (
  2 2^(14/39) Sqrt[Pi]
    Csc[Pi/13] Gamma[1/39] Gamma[7/39] Sin[Pi/39] Sin[(7 Pi)/
    39])/(3^(11/26) Gamma[1/13] Gamma[4/13]), 
 Gamma[29/78] -> (
  3^(1/13) Gamma[1/39] Gamma[4/39] Gamma[7/39] Sec[(5 Pi)/
    39] Sqrt[Pi Cos[(19 Pi)/78] Csc[(2 Pi)/39] Csc[Pi/
     13] Csc[(5 Pi)/39] Sec[(5 Pi)/26] Sin[Pi/39] Sin[(
     4 Pi)/39] Sin[(7 Pi)/39]])/(
  2^(29/39) 13^(1/12) Gamma[2/39] Gamma[1/13] Gamma[4/13]), 
 Gamma[31/78] -> (
  2 2^(8/39) 3^(3/26) Sqrt[Pi]
    Gamma[4/39] Gamma[5/13] Sin[(4 Pi)/39])/(
  Gamma[5/39] Gamma[6/13]), 
 Gamma[35/78] -> (Sqrt[Pi] Gamma[2/39] Sec[(2 Pi)/39])/(
  2^(35/39) Gamma[4/39]), 
 Gamma[37/78] -> (Sqrt[Pi] Gamma[1/39] Sec[Pi/39])/(
  2^(37/39) Gamma[2/39]), 
 Gamma[27/80] -> ((5 + Sqrt[5])^(1/4)
    Gamma[3/80] Gamma[1/16]^2 Gamma[9/80] Gamma[19/80] Gamma[2/
    5] Sqrt[Csc[Pi/80] Csc[(7 Pi)/80] Csc[(11 Pi)/80] Csc[(
     17 Pi)/80] Sec[(13 Pi)/80] Sin[(3 Pi)/80] Sin[(9 Pi)/
     80] Sin[(19 Pi)/80] Tan[Pi/16]])/(
  2 2^(1/8) Gamma[1/80] Gamma[7/80] Gamma[1/8] Gamma[11/80] Gamma[17/
    80]), 
 Gamma[29/80] -> (
  Sqrt[Pi]
    Csc[(13 Pi)/80] Gamma[3/80] Gamma[1/16] Gamma[19/80] Sec[Pi/
    16] Sec[(11 Pi)/80])/(
  4 2^(7/8) 5^(5/16) Gamma[1/8] Gamma[13/80] Gamma[3/16]), 
 Gamma[31/80] -> (
  Sqrt[5 + Sqrt[5]]
    Cos[Pi/8] Csc[(7 Pi)/80] Csc[(13 Pi)/80] Gamma[3/
    80] Gamma[1/16]^2 Gamma[9/80]^2 Gamma[1/5] Gamma[19/80]^2 Gamma[1/
    4] Gamma[2/5] Sec[Pi/16] Sec[(3 Pi)/16] Sec[(17 Pi)/
    80] Sin[(9 Pi)/80] Sin[(19 Pi)/80])/(
  2 2^(5/8) 5^(1/4)
    Gamma[1/80] Gamma[7/80] Gamma[1/8]^3 Gamma[11/80] Gamma[13/
    80] Gamma[21/80] Gamma[23/80]), 
 Gamma[33/80] -> (
  5^(3/16) Sqrt[5 + Sqrt[5]]
    Cos[Pi/8] Csc[Pi/80] Csc[(7 Pi)/80] Csc[(13 Pi)/
    80] Csc[(17 Pi)/80] Gamma[3/80] Gamma[1/16]^3 Gamma[9/
    80]^2 Gamma[3/16] Gamma[1/5] Gamma[19/80]^2 Gamma[1/4] Gamma[2/
    5] Sec[(7 Pi)/80] Sec[(3 Pi)/16] Sec[(17 Pi)/80] Sin[(
    9 Pi)/80] Sin[(19 Pi)/80] Tan[Pi/16])/(
  8 2^(5/8) Gamma[1/80]^2 Gamma[7/80] Gamma[1/8]^3 Gamma[11/80] Gamma[
    13/80] Gamma[17/80] Gamma[21/80] Gamma[23/80]), 
 Gamma[37/80] -> (
  2 5^(3/16) (5 + Sqrt[5])^(1/4)
    Cos[Pi/8] Gamma[3/80] Gamma[1/16] Gamma[9/80] Gamma[3/
    16] Gamma[19/80] Gamma[1/4] Gamma[2/5] Sec[(3 Pi)/16] Sqrt[
   Cos[(13 Pi)/80] Csc[Pi/80] Csc[(7 Pi)/80] Csc[(17 Pi)/
     80] Sin[(3 Pi)/80] Sin[(9 Pi)/80] Sin[(11 Pi)/80] Sin[(
     19 Pi)/80] Tan[Pi/16]])/(
  Gamma[1/80] Gamma[7/80] Gamma[1/8]^2 Gamma[17/80] Gamma[21/80]), 
 Gamma[39/80] -> (
  5^(1/16) Sqrt[Pi]
    Cos[Pi/8] Csc[(7 Pi)/80] Gamma[1/16] Gamma[9/80] Gamma[3/
    16] Gamma[1/4] Sec[Pi/80] Sec[(3 Pi)/16] Sec[(17 Pi)/
    80])/(4 2^(3/4) Gamma[7/80] Gamma[1/8]^2 Gamma[23/80]), 
 Gamma[1/82] -> (
  Csc[Pi/82] Gamma[1/41] Gamma[20/41] Sin[Pi/41])/(
  2^(1/41) Sqrt[Pi]), 
 Gamma[3/82] -> (
  Csc[(3 Pi)/82] Gamma[3/41] Gamma[19/41] Sin[(3 Pi)/41])/(
  2^(3/41) Sqrt[Pi]), 
 Gamma[5/82] -> (
  Csc[(5 Pi)/82] Gamma[5/41] Gamma[18/41] Sin[(5 Pi)/41])/(
  2^(5/41) Sqrt[Pi]), 
 Gamma[7/82] -> (
  Csc[(7 Pi)/82] Gamma[7/41] Gamma[17/41] Sin[(7 Pi)/41])/(
  2^(7/41) Sqrt[Pi]), 
 Gamma[9/82] -> (
  Csc[(9 Pi)/82] Gamma[9/41] Gamma[16/41] Sin[(9 Pi)/41])/(
  2^(9/41) Sqrt[Pi]), 
 Gamma[11/82] -> (
  Cos[(19 Pi)/82] Csc[(11 Pi)/82] Gamma[11/41] Gamma[15/41])/(
  2^(11/41) Sqrt[Pi]), 
 Gamma[13/82] -> (
  Cos[(15 Pi)/82] Csc[(13 Pi)/82] Gamma[13/41] Gamma[14/41])/(
  2^(13/41) Sqrt[Pi]), 
 Gamma[15/82] -> (
  Cos[(11 Pi)/82] Csc[(15 Pi)/82] Gamma[13/41] Gamma[15/41])/(
  2^(15/41) Sqrt[Pi]), 
 Gamma[17/82] -> (
  Cos[(7 Pi)/82] Csc[(17 Pi)/82] Gamma[12/41] Gamma[17/41])/(
  2^(17/41) Sqrt[Pi]), 
 Gamma[19/82] -> (
  Cos[(3 Pi)/82] Csc[(19 Pi)/82] Gamma[11/41] Gamma[19/41])/(
  2^(19/41) Sqrt[Pi]), 
 Gamma[21/82] -> (Sqrt[Pi] Gamma[10/41] Sec[(10 Pi)/41])/(
  2^(21/41) Gamma[20/41]), 
 Gamma[23/82] -> (Sqrt[Pi] Gamma[9/41] Sec[(9 Pi)/41])/(
  2^(23/41) Gamma[18/41]), 
 Gamma[25/82] -> (Sqrt[Pi] Gamma[8/41] Sec[(8 Pi)/41])/(
  2^(25/41) Gamma[16/41]), 
 Gamma[27/82] -> (Sqrt[Pi] Gamma[7/41] Sec[(7 Pi)/41])/(
  2^(27/41) Gamma[14/41]), 
 Gamma[29/82] -> (Sqrt[Pi] Gamma[6/41] Sec[(6 Pi)/41])/(
  2^(29/41) Gamma[12/41]), 
 Gamma[31/82] -> (Sqrt[Pi] Gamma[5/41] Sec[(5 Pi)/41])/(
  2^(31/41) Gamma[10/41]), 
 Gamma[33/82] -> (Sqrt[Pi] Gamma[4/41] Sec[(4 Pi)/41])/(
  2^(33/41) Gamma[8/41]), 
 Gamma[35/82] -> (Sqrt[Pi] Gamma[3/41] Sec[(3 Pi)/41])/(
  2^(35/41) Gamma[6/41]), 
 Gamma[37/82] -> (Sqrt[Pi] Gamma[2/41] Sec[(2 Pi)/41])/(
  2^(37/41) Gamma[4/41]), 
 Gamma[39/82] -> (Sqrt[Pi] Gamma[1/41] Sec[Pi/41])/(
  2^(39/41) Gamma[2/41]), 
 Gamma[13/84] -> (
  8 2^(1/14) 3^(1/7) 7^(5/24)
    Cos[(5 Pi)/42] Cos[(5 Pi)/28] Csc[Pi/7] Gamma[2/
    21] Gamma[3/28] Gamma[1/4] Sqrt[
   Cos[Pi/84] Cos[Pi/14] Cos[(11 Pi)/84] Cos[(17 Pi)/
     84] Csc[(3 Pi)/28] Csc[(13 Pi)/84] Csc[(4 Pi)/21] Csc[(
     19 Pi)/84] Sec[(5 Pi)/84] Sin[Pi/28] Sin[Pi/21] Sin[(
     2 Pi)/21] Sin[(5 Pi)/28]])/(Gamma[1/84] Gamma[2/7]), 
 Gamma[17/84] -> (
  Csc[(3 Pi)/14] Gamma[1/28] Gamma[11/84] Gamma[2/7] Sin[(
    11 Pi)/84])/(2^(3/7) 3^(3/28) Gamma[3/28] Gamma[1/7]), 
 Gamma[19/84] -> (
  2^(6/7) (-1 + Sqrt[3]) Pi Cos[(13 Pi)/84] Cos[(5 Pi)/
    28] Csc[(2 Pi)/21] Gamma[1/28] Gamma[1/21] Gamma[5/84] Sec[(
    5 Pi)/42] Sec[(3 Pi)/14] Sin[(5 Pi)/84] Sqrt[
   Cos[Pi/84] Cos[(11 Pi)/84] Csc[(3 Pi)/28] Csc[(19 Pi)/
     84] Sec[(5 Pi)/84] Sec[Pi/14] Sec[(17 Pi)/84] Sin[Pi/
     28] Sin[Pi/7] Sin[(13 Pi)/84] Sin[(5 Pi)/28]]
    Sin[(4 Pi)/21])/(
  3^(9/28) 7^(1/8) Gamma[2/21] Gamma[1/7] Gamma[1/4] Gamma[3/7]), 
 Gamma[23/84] -> (Pi Cos[(5 Pi)/28] Csc[(19 Pi)/84] Gamma[1/
    28] Gamma[5/84] Sec[(5 Pi)/84] Sec[Pi/14] Sec[(19 Pi)/
    84] Sqrt[
   Cos[(3 Pi)/14] Csc[(3 Pi)/28] Csc[Pi/7] Sin[Pi/
     28] Sin[(5 Pi)/28]])/(
  4 2^(2/7) 3^(9/28) 7^(1/8) Gamma[1/7] Gamma[1/4] Gamma[3/7]), 
 Gamma[25/84] -> (
  2^(11/14) 7^(1/12)
    Csc[(3 Pi)/14] Gamma[1/28] Gamma[11/84] Gamma[2/7] Sin[(
    11 Pi)/84] Sqrt[
   Csc[Pi/21] Csc[(4 Pi)/21] Sin[(2 Pi)/21] Sin[Pi/7]]
    Sin[(17 Pi)/84])/(3^(1/14) Gamma[1/21] Gamma[3/28]), 
 Gamma[29/84] -> (
  8 3^(13/28) 7^(1/8) Cos[(5 Pi)/28] Gamma[3/28] Gamma[1/4] Sqrt[
   Cos[Pi/84] Cos[Pi/14] Cos[(11 Pi)/84] Cos[(17 Pi)/
     84] Csc[(3 Pi)/28] Csc[Pi/7] Csc[(19 Pi)/84] Sec[(
     5 Pi)/84] Sin[Pi/28] Sin[(13 Pi)/84] Sin[(5 Pi)/
     28]])/Gamma[1/84], 
 Gamma[31/84] -> (
  3^(9/28) 7^(1/12) Sqrt[1 + (-1)^(2/21)/(1 + (-1)^(4/21))]
    Csc[(2 Pi)/21] Csc[(3 Pi)/14] Gamma[11/84] Gamma[2/7] Sin[(
    11 Pi)/84] Sin[(4 Pi)/21])/(2^(3/14) Gamma[1/21]), 
 Gamma[37/84] -> (
  2^(6/7) (-1 + Sqrt[3]) Pi Cos[(13 Pi)/84] Csc[(2 Pi)/
    21] Gamma[1/21] Gamma[5/84] Sec[(5 Pi)/42] Sin[(5 Pi)/
    84] Sin[(4 Pi)/21] Sqrt[
   Cos[Pi/84] Cos[(11 Pi)/84] Sec[(5 Pi)/84] Sec[Pi/
     14] Sec[(17 Pi)/84] Sec[(3 Pi)/14] Sin[(13 Pi)/84] Sin[(
     19 Pi)/84]])/(3^(1/7) Gamma[2/21] Gamma[1/7] Gamma[3/7]), 
 Gamma[41/84] -> (Pi Gamma[1/84] Sec[Pi/84] Sec[Pi/14] Sec[(
    5 Pi)/42] Sec[(3 Pi)/14] Sin[Pi/7]^(3/2) Sqrt[
   Csc[Pi/21] Csc[(2 Pi)/21] Sin[(4 Pi)/21]])/(
  4 2^(13/14) 3^(3/28) 7^(1/12) Gamma[2/21] Gamma[3/7]), 
 Gamma[28/85] -> (
  Csc[(11 Pi)/85] Gamma[6/85] Gamma[23/85] Gamma[8/17] Sec[(
    29 Pi)/170])/(4 5^(5/34) Gamma[11/85] Gamma[6/17]), 
 Gamma[29/85] -> (
  Gamma[1/85] Gamma[3/85] Gamma[6/85] Gamma[8/85] Gamma[2/17] Gamma[
    13/85] Gamma[18/85] Gamma[4/17] Gamma[23/85] Gamma[7/17] Sqrt[
   Cos[(3 Pi)/34] Cos[(39 Pi)/170] Csc[(2 Pi)/85] Csc[(
     4 Pi)/85] Csc[(7 Pi)/85] Csc[(9 Pi)/85] Csc[(12 Pi)/
     85] Csc[(14 Pi)/85] Csc[(19 Pi)/85] Sec[(27 Pi)/
     170] Sec[(37 Pi)/170] Sin[Pi/85] Sin[(3 Pi)/85] Sin[(
     6 Pi)/85] Sin[(8 Pi)/85] Sin[(2 Pi)/17] Sin[(13 Pi)/
     85] Sin[(18 Pi)/85] Sin[(4 Pi)/17]])/(
  5^(7/34) 17^(1/10) (5/8 - Sqrt[5]/8)^(1/4)
    Gamma[2/85] Gamma[4/85] Gamma[7/85] Gamma[9/85] Gamma[12/
    85] Gamma[14/85] Gamma[1/5] Gamma[19/85] Gamma[24/85]), 
 Gamma[32/85] -> (
  17^(1/10) Cos[(39 Pi)/170] Csc[(4 Pi)/85] Csc[(9 Pi)/
    85] Csc[(11 Pi)/85] Csc[(14 Pi)/85] Csc[(16 Pi)/85] Csc[(
    21 Pi)/85] Gamma[1/85] Gamma[3/85]^2 Gamma[6/85] Gamma[8/
    85]^2 Gamma[13/85]^2 Gamma[18/85]^2 Gamma[4/17]^2 Gamma[23/
    85]^2 Gamma[5/17] Gamma[2/5] Gamma[7/17] Sec[(23 Pi)/170] Sec[(
    33 Pi)/170] Sin[(3 Pi)/85] Sin[(8 Pi)/85] Sin[(13 Pi)/
    85] Sin[(18 Pi)/85] Sin[(4 Pi)/17])/(
  4 5^(23/34)
    Gamma[2/85] Gamma[4/85] Gamma[1/17] Gamma[7/85] Gamma[9/85] Gamma[
    11/85] Gamma[12/85] Gamma[14/85] Gamma[3/17] Gamma[16/85] Gamma[1/
    5] Gamma[21/85] Gamma[22/85] Gamma[26/85] Gamma[27/85] Gamma[31/
    85]), Gamma[33/85] -> (
  Csc[(16 Pi)/85] Gamma[1/85] Gamma[18/85] Gamma[7/17] Sec[(
    19 Pi)/170])/(4 5^(15/34) Gamma[1/17] Gamma[16/85]), 
 Gamma[36/85] -> (17^(1/10)
      Csc[(2 Pi)/85] Csc[(4 Pi)/85] Csc[(9 Pi)/85] Csc[(
      11 Pi)/85] Csc[(14 Pi)/85] Csc[(16 Pi)/85] Csc[(
      19 Pi)/85]^2 Csc[(21 Pi)/85] Gamma[1/85] Gamma[3/
      85]^2 Gamma[6/85] Gamma[8/85]^2 Gamma[2/17] Gamma[13/
      85]^2 Gamma[18/85]^2 Gamma[4/17]^2 Gamma[23/85]^2 Gamma[5/
      17] Gamma[2/5] Gamma[7/17] Sin[(3 Pi)/85] Sin[(13 Pi)/
      170] Sin[(8 Pi)/85] Sin[(19 Pi)/170] Sin[(2 Pi)/
      17] Sin[(23 Pi)/170] Sin[(33 Pi)/170] Sin[(18 Pi)/
      85] Sin[(4 Pi)/17])/(5^(5/17)
      Gamma[2/85]^2 Gamma[4/85] Gamma[1/17] Gamma[7/85] Gamma[9/
      85] Gamma[11/85] Gamma[12/85] Gamma[14/85] Gamma[16/85] Gamma[1/
      5] Gamma[19/85] Gamma[21/85] Gamma[22/85] Gamma[26/85] Gamma[27/
      85] Gamma[31/85]), 
 Gamma[37/85] -> (
  4 5^(11/34)
    Cos[(23 Pi)/170] Gamma[14/85] Gamma[3/17] Gamma[31/85] Sin[(
    14 Pi)/85])/(Gamma[3/85] Gamma[4/17]), 
 Gamma[38/85] -> (
  5^(9/34) Csc[(4 Pi)/85] Csc[(21 Pi)/85] Gamma[13/85] Gamma[4/
    17] Gamma[6/17] Sec[(9 Pi)/170] Sin[(4 Pi)/17])/(
  4 Gamma[4/85] Gamma[21/85]), 
 Gamma[39/85] -> (4 Gamma[1/85] Gamma[3/85] Gamma[6/85] Gamma[8/
      85] Gamma[2/17] Gamma[13/85] Gamma[18/85] Gamma[4/17] Gamma[23/
      85] Gamma[5/17] Gamma[7/17] Sqrt[
     Cos[(3 Pi)/34] Cos[(27 Pi)/170] Cos[(39 Pi)/170] Csc[(
       2 Pi)/85] Csc[(4 Pi)/85] Csc[(7 Pi)/85] Csc[(9 Pi)/
       85] Csc[(14 Pi)/85] Csc[(19 Pi)/85] Sec[(37 Pi)/
       170] Sin[Pi/85] Sin[(3 Pi)/85] Sin[(6 Pi)/85] Sin[(
       8 Pi)/85] Sin[(2 Pi)/17] Sin[(12 Pi)/85] Sin[(
       13 Pi)/85] Sin[(18 Pi)/85] Sin[(4 Pi)/17]])/(17^(
     1/10) (5/8 - Sqrt[5]/8)^(1/4)
      Gamma[2/85] Gamma[4/85] Gamma[1/17] Gamma[7/85] Gamma[9/
      85] Gamma[14/85] Gamma[1/5] Gamma[19/85] Gamma[22/85] Gamma[24/
      85]), Gamma[41/85] -> (
  5^(3/34) Cos[(3 Pi)/34] Csc[(7 Pi)/85] Gamma[2/17] Gamma[27/
    85] Gamma[7/17] Sec[(3 Pi)/170] Sec[(37 Pi)/170])/(
  4 Gamma[7/85] Gamma[24/85]), 
 Gamma[42/85] -> (
  4 5^(1/34)
    Cos[(33 Pi)/170] Gamma[9/85] Gamma[26/85] Gamma[8/17] Sin[(
    9 Pi)/85])/(Gamma[8/85] Gamma[5/17]), 
 Gamma[1/86] -> (
  Csc[Pi/86] Gamma[1/43] Gamma[21/43] Sin[Pi/43])/(
  2^(1/43) Sqrt[Pi]), 
 Gamma[3/86] -> (
  Csc[(3 Pi)/86] Gamma[3/43] Gamma[20/43] Sin[(3 Pi)/43])/(
  2^(3/43) Sqrt[Pi]), 
 Gamma[5/86] -> (
  Csc[(5 Pi)/86] Gamma[5/43] Gamma[19/43] Sin[(5 Pi)/43])/(
  2^(5/43) Sqrt[Pi]), 
 Gamma[7/86] -> (
  Csc[(7 Pi)/86] Gamma[7/43] Gamma[18/43] Sin[(7 Pi)/43])/(
  2^(7/43) Sqrt[Pi]), 
 Gamma[9/86] -> (
  Csc[(9 Pi)/86] Gamma[9/43] Gamma[17/43] Sin[(9 Pi)/43])/(
  2^(9/43) Sqrt[Pi]), 
 Gamma[11/86] -> (
  Cos[(21 Pi)/86] Csc[(11 Pi)/86] Gamma[11/43] Gamma[16/43])/(
  2^(11/43) Sqrt[Pi]), 
 Gamma[13/86] -> (
  Cos[(17 Pi)/86] Csc[(13 Pi)/86] Gamma[13/43] Gamma[15/43])/(
  2^(13/43) Sqrt[Pi]), 
 Gamma[15/86] -> (
  Cos[(13 Pi)/86] Csc[(15 Pi)/86] Gamma[14/43] Gamma[15/43])/(
  2^(15/43) Sqrt[Pi]), 
 Gamma[17/86] -> (
  Cos[(9 Pi)/86] Csc[(17 Pi)/86] Gamma[13/43] Gamma[17/43])/(
  2^(17/43) Sqrt[Pi]), 
 Gamma[19/86] -> (
  Cos[(5 Pi)/86] Csc[(19 Pi)/86] Gamma[12/43] Gamma[19/43])/(
  2^(19/43) Sqrt[Pi]), 
 Gamma[21/86] -> (
  Cos[Pi/86] Csc[(21 Pi)/86] Gamma[11/43] Gamma[21/43])/(
  2^(21/43) Sqrt[Pi]), 
 Gamma[23/86] -> (Sqrt[Pi] Gamma[10/43] Sec[(10 Pi)/43])/(
  2^(23/43) Gamma[20/43]), 
 Gamma[25/86] -> (Sqrt[Pi] Gamma[9/43] Sec[(9 Pi)/43])/(
  2^(25/43) Gamma[18/43]), 
 Gamma[27/86] -> (Sqrt[Pi] Gamma[8/43] Sec[(8 Pi)/43])/(
  2^(27/43) Gamma[16/43]), 
 Gamma[29/86] -> (Sqrt[Pi] Gamma[7/43] Sec[(7 Pi)/43])/(
  2^(29/43) Gamma[14/43]), 
 Gamma[31/86] -> (Sqrt[Pi] Gamma[6/43] Sec[(6 Pi)/43])/(
  2^(31/43) Gamma[12/43]), 
 Gamma[33/86] -> (Sqrt[Pi] Gamma[5/43] Sec[(5 Pi)/43])/(
  2^(33/43) Gamma[10/43]), 
 Gamma[35/86] -> (Sqrt[Pi] Gamma[4/43] Sec[(4 Pi)/43])/(
  2^(35/43) Gamma[8/43]), 
 Gamma[37/86] -> (Sqrt[Pi] Gamma[3/43] Sec[(3 Pi)/43])/(
  2^(37/43) Gamma[6/43]), 
 Gamma[39/86] -> (Sqrt[Pi] Gamma[2/43] Sec[(2 Pi)/43])/(
  2^(39/43) Gamma[4/43]), 
 Gamma[41/86] -> (Sqrt[Pi] Gamma[1/43] Sec[Pi/43])/(
  2^(41/43) Gamma[2/43]), 
 Gamma[16/87] -> (Csc[(16 Pi)/87] Gamma[13/87] Gamma[14/29])/(
  2 3^(3/58) Gamma[13/29]), 
 Gamma[19/87] -> (Csc[(19 Pi)/87] Gamma[10/87] Gamma[13/29])/(
  2 3^(9/58) Gamma[10/29]), 
 Gamma[22/87] -> (Gamma[7/87] Gamma[12/29] Sec[(43 Pi)/174])/(
  2 3^(15/58) Gamma[7/29]), 
 Gamma[25/87] -> (Gamma[4/87] Gamma[11/29] Sec[(37 Pi)/174])/(
  2 3^(21/58) Gamma[4/29]), 
 Gamma[26/87] -> (
  Gamma[1/87] Gamma[4/87] Gamma[2/29] Gamma[7/87] Gamma[10/87] Gamma[
    13/87] Gamma[5/29] Gamma[8/29] Gamma[11/29] Gamma[14/29] Sqrt[
   2 Cos[Pi/58] Cos[(7 Pi)/58] Cos[(13 Pi)/58] Csc[(2 Pi)/
     87] Csc[(5 Pi)/87] Csc[(8 Pi)/87] Csc[(11 Pi)/87] Csc[(
     14 Pi)/87] Csc[(17 Pi)/87] Csc[(20 Pi)/87] Sec[(
     35 Pi)/174] Sec[(41 Pi)/174] Sin[Pi/87] Sin[(4 Pi)/
     87] Sin[(2 Pi)/29] Sin[(7 Pi)/87] Sin[(10 Pi)/87] Sin[(
     13 Pi)/87] Sin[(5 Pi)/29]])/(
  3^(95/116) 29^(1/12)
    Gamma[2/87] Gamma[5/87] Gamma[8/87] Gamma[11/87] Gamma[14/
    87] Gamma[17/87] Gamma[20/87] Gamma[23/87] Gamma[1/3]), 
 Gamma[28/87] -> (Gamma[1/87] Gamma[10/29] Sec[(31 Pi)/174])/(
  2 3^(27/58) Gamma[1/29]), 
 Gamma[31/87] -> (
  2 3^(25/58) Gamma[2/29] Gamma[9/29] Sin[(2 Pi)/29])/(
  Gamma[2/87] - 2 Gamma[2/87] Sin[(7 Pi)/58]), 
 Gamma[32/87] -> (2 Gamma[1/87] Gamma[4/87] Gamma[2/29] Gamma[7/
      87] Gamma[3/29] Gamma[10/87] Gamma[13/87] Gamma[5/29] Gamma[8/
      29] Gamma[11/29] Gamma[14/29] Sqrt[
     2 Cos[Pi/58] Cos[(7 Pi)/58] Cos[(35 Pi)/174] Cos[(
       13 Pi)/58] Csc[(2 Pi)/87] Csc[(5 Pi)/87] Csc[(
       8 Pi)/87] Csc[(11 Pi)/87] Csc[(14 Pi)/87] Csc[(
       17 Pi)/87] Csc[(20 Pi)/87] Sec[(41 Pi)/174] Sin[Pi/
       87] Sin[(4 Pi)/87] Sin[(2 Pi)/29] Sin[(7 Pi)/87] Sin[(
       10 Pi)/87] Sin[(13 Pi)/87] Sin[(5 Pi)/29]])/(3^(
     49/116) 29^(1/12)
      Gamma[2/87] Gamma[1/29] Gamma[5/87] Gamma[8/87] Gamma[11/
      87] Gamma[14/87] Gamma[17/87] Gamma[20/87] Gamma[23/87] Gamma[1/
      3]), Gamma[34/87] -> (
  2 3^(19/58) Gamma[5/29] Gamma[8/29] Sin[(5 Pi)/29])/(
  Gamma[5/87] - 2 Gamma[5/87] Sin[(3 Pi)/58]), 
 Gamma[35/87] -> (
  2 3^(17/58) Cos[(41 Pi)/174] Gamma[6/29] Gamma[23/87])/
  Gamma[2/29], 
 Gamma[37/87] -> (
  2 3^(13/58) Cos[(13 Pi)/58] Gamma[7/29] Gamma[8/29])/(
  Gamma[8/87] + 2 Gamma[8/87] Sin[Pi/58]), 
 Gamma[38/87] -> (
  2 3^(11/58) Gamma[20/87] Gamma[9/29] Sin[(20 Pi)/87])/
  Gamma[3/29], 
 Gamma[40/87] -> (
  2 3^(7/58) Cos[(7 Pi)/58] Gamma[6/29] Gamma[11/29])/(
  Gamma[11/87] + 2 Gamma[11/87] Sin[(5 Pi)/58]), 
 Gamma[41/87] -> (
  2 3^(5/58) Gamma[17/87] Gamma[12/29] Sin[(17 Pi)/87])/
  Gamma[4/29], 
 Gamma[43/87] -> (2 3^(1/58) Cos[Pi/58] Gamma[5/29] Gamma[14/29])/(
  Gamma[14/87] + 2 Gamma[14/87] Sin[(9 Pi)/58]), 
 Gamma[29/88] -> (
  Gamma[1/88] Gamma[3/88] Gamma[9/88] Gamma[2/11] Gamma[17/88] Gamma[
    25/88] Sqrt[Pi Cos[(19 Pi)/88] Csc[(5 Pi)/88] Csc[(
     7 Pi)/88] Csc[Pi/11] Csc[(13 Pi)/88] Csc[(21 Pi)/
     88] Sec[(3 Pi)/22] Sec[(15 Pi)/88] Sin[Pi/88] Sin[(
     3 Pi)/88] Sin[(9 Pi)/88] Sin[(2 Pi)/11] Sin[(17 Pi)/
     88]])/(2^(29/44) 11^(1/4)
    Gamma[5/88] Gamma[7/88] Gamma[1/11] Gamma[13/88] Gamma[21/
    88] Gamma[4/11]), 
 Gamma[31/88] -> (
  Sqrt[Pi]
    Cos[(19 Pi)/88] Csc[(7 Pi)/88] Csc[(15 Pi)/88] Gamma[1/
    88] Gamma[3/88] Gamma[9/88] Gamma[17/88]^2 Gamma[25/88]^2 Gamma[5/
    11] Sec[Pi/8] Sec[(13 Pi)/88] Sec[(21 Pi)/88] Sin[(
    3 Pi)/88] Sin[(17 Pi)/88])/(
  4 2^(5/44) 11^(3/8)
    Gamma[5/88] Gamma[7/88] Gamma[15/88] Gamma[19/88] Gamma[1/
    4] Gamma[23/88] Gamma[27/88] Gamma[4/11]), 
 Gamma[35/88] -> (
  2^(1/44) Sqrt[Pi]
    Cos[(19 Pi)/88] Csc[(7 Pi)/88] Csc[(15 Pi)/88] Gamma[1/
    88] Gamma[3/88] Gamma[9/88]^2 Gamma[2/11] Gamma[17/88]^2 Gamma[25/
    88]^2 Gamma[5/11] Sec[Pi/8] Sec[(21 Pi)/88] Sin[(3 Pi)/
    88] Sin[(9 Pi)/88] Sin[(17 Pi)/88])/(
  11^(3/8) Gamma[5/88] Gamma[7/88] Gamma[1/11] Gamma[13/88] Gamma[15/
    88] Gamma[19/88] Gamma[1/4] Gamma[23/88] Gamma[27/88] Gamma[4/
    11]), Gamma[37/88] -> (
  Csc[(15 Pi)/88] Gamma[1/88] Gamma[3/88] Gamma[9/88] Gamma[17/
    88] Gamma[25/88] Sec[(7 Pi)/
    88] Sqrt[Pi Cos[(3 Pi)/22] Cos[(19 Pi)/88] Csc[(5 Pi)/
     88] Csc[(7 Pi)/88] Csc[Pi/11] Csc[(13 Pi)/88] Csc[(
     2 Pi)/11] Csc[(21 Pi)/88] Sec[(15 Pi)/88] Sin[Pi/
     88] Sin[(3 Pi)/88] Sin[(9 Pi)/88] Sin[(17 Pi)/88]])/(
  4 2^(39/44) 11^(1/4)
    Gamma[5/88] Gamma[1/11] Gamma[13/88] Gamma[15/88] Gamma[21/88]), 
 Gamma[39/88] -> (Pi Csc[(17 Pi)/88] Gamma[5/88] Gamma[27/
    88] Sec[(5 Pi)/88] Sec[(5 Pi)/22])/(
  4 2^(13/22) Gamma[17/88] Gamma[3/11] Gamma[5/11]), 
 Gamma[41/88] -> (
  2 2^(1/22) Pi Cos[(19 Pi)/88] Gamma[3/88] Gamma[25/88] Sec[(
    5 Pi)/22] Sin[(3 Pi)/88])/(
  Gamma[19/88] Gamma[3/11] Gamma[4/11]), 
 Gamma[43/88] -> (
  2^(15/22) Pi Cos[(21 Pi)/88] Csc[Pi/11] Gamma[1/88] Gamma[
    23/88] Sin[Pi/88])/(Gamma[1/11] Gamma[21/88] Gamma[5/11]), 
 Gamma[1/90] -> (
  64 2^(131/180) 5^(1/12) (5 - Sqrt[5])^(1/4)
    Cos[(7 Pi)/45] Gamma[1/45] Gamma[8/45] Gamma[1/5] Gamma[1/
    3] Sin[(13 Pi)/90] Sqrt[(
   Cos[Pi/45] Cos[(2 Pi)/45] Cos[Pi/18] Cos[(4 Pi)/
     45] Cos[(11 Pi)/45] Csc[(2 Pi)/15] Sec[(8 Pi)/
     45] Sin[Pi/15] Sin[Pi/9] Sin[(19 Pi)/90])/Pi]
    Sin[(2 Pi)/9]^2 Tan[(17 Pi)/90])/(
  3^(1/60) Gamma[1/15] Gamma[7/45]), 
 Gamma[7/90] -> (
  3^(11/60) (3 + Sqrt[5])^(3/4)
    Cos[Pi/90] Cot[(13 Pi)/90] Cot[(17 Pi)/90] Csc[(7 Pi)/
    90] Csc[(2 Pi)/9] Gamma[1/15] Gamma[7/45] Gamma[11/45] Gamma[2/
    5] Sec[Pi/45] Sec[(11 Pi)/45] Sin[(7 Pi)/45] Sqrt[(
   Cos[(19 Pi)/90] Csc[Pi/15] Csc[(8 Pi)/45] Sec[Pi/
     18] Sin[Pi/45] Sin[(2 Pi)/45] Sin[(4 Pi)/45] Sin[(
     2 Pi)/15] Sin[(11 Pi)/45])/Pi])/(
  2 2^(73/180) Gamma[4/45] Gamma[1/5]), 
 Gamma[11/90] -> (
  3^(11/60) (3 + Sqrt[5])^(3/4)
    Cos[Pi/90] Cos[(8 Pi)/45] Cot[(17 Pi)/90] Csc[(13 Pi)/
    90] Csc[(2 Pi)/9] Gamma[1/45] Gamma[1/15] Gamma[2/9] Gamma[11/
    45]^2 Gamma[2/5] Sec[Pi/45] Sec[(11 Pi)/45] Sqrt[(
   Cos[(19 Pi)/90] Csc[Pi/15] Csc[(8 Pi)/45] Sec[Pi/
     18] Sin[Pi/45] Sin[(2 Pi)/45] Sin[(4 Pi)/45] Sin[(
     2 Pi)/15] Sin[(11 Pi)/45])/Pi])/(
  2 2^(89/180) 5^(7/18)
    Gamma[4/45] Gamma[1/9] Gamma[8/45] Gamma[1/5]), 
 Gamma[13/90] -> (
  64 2^(83/180)
    Cos[Pi/90] Cos[(7 Pi)/45] Gamma[1/45] Gamma[2/45]^2 Gamma[2/
    9] Gamma[11/45]^2 Gamma[1/3]^2 Sin[Pi/9] Sin[(2 Pi)/
    9]^2 Sqrt[(
   Cos[(19 Pi)/90] Csc[(8 Pi)/45] Sec[Pi/18] Sin[Pi/
     45] Sin[(2 Pi)/45] Sin[(4 Pi)/45] Sin[(11 Pi)/
     45])/Pi])/(
  3^(1/6) 5^(7/12) (5 - Sqrt[5])^(1/4)
    Gamma[4/45] Gamma[1/9]^2 Gamma[7/45] Gamma[8/45] Gamma[1/5]), 
 Gamma[17/90] -> (
  64 2^(157/180) (3 + Sqrt[5])^(1/4)
    Cos[Pi/90] Cos[(7 Pi)/45] Gamma[1/45]^2 Gamma[2/45] Gamma[2/
    9] Gamma[11/45]^2 Gamma[1/3] Gamma[2/5] Sin[Pi/9] Sin[(
    13 Pi)/90] Sin[(2 Pi)/9]^2 Sqrt[(
   Cos[(19 Pi)/90] Csc[(2 Pi)/15] Csc[(8 Pi)/45] Sec[Pi/
     18] Sin[Pi/45] Sin[(2 Pi)/45] Sin[Pi/15] Sin[(4 Pi)/
     45] Sin[(11 Pi)/45])/Pi])/(
  3^(7/12) 5^(2/3)
    Gamma[4/45] Gamma[1/9]^2 Gamma[7/45] Gamma[8/45] Gamma[1/5]), 
 Gamma[19/90] -> (
  16 2^(59/180) (5 + Sqrt[5])^(1/4)
    Cos[Pi/90] Cos[(17 Pi)/90] Gamma[1/45] Gamma[2/45] Gamma[1/
    15] Gamma[2/9] Gamma[11/45]^2 Gamma[1/3] Gamma[2/5] Sin[(2 Pi)/
    9] Sqrt[(
   Cos[(4 Pi)/45] Cot[(8 Pi)/45] Cot[(19 Pi)/90] Sin[(
     4 Pi)/45] Sin[Pi/9] Tan[Pi/45] Tan[(2 Pi)/45] Tan[(
     11 Pi)/45])/((5 - Sqrt[5]) Pi)])/(
  3^(2/5) 5^(11/36)
    Gamma[4/45]^2 Gamma[1/9] Gamma[8/45] Gamma[1/5]^2), 
 Gamma[23/90] -> (
  16 2^(43/180)
    Cos[Pi/90] Cos[(13 Pi)/90] Cos[(17 Pi)/90] Csc[(2 Pi)/
    9] Gamma[1/15] Gamma[7/45] Gamma[11/45] Sec[(11 Pi)/45] Sin[(
    7 Pi)/
    45] Sqrt[Pi Cos[(19 Pi)/90] Csc[(8 Pi)/45] Sec[Pi/
     18] Sin[Pi/45] Sin[(2 Pi)/45] Sin[(4 Pi)/45] Sin[(
     11 Pi)/45]])/(
  3^(7/30) 5^(1/12) (5 - Sqrt[5])^(1/4)
    Gamma[8/45] Gamma[1/5] Gamma[1/3]), 
 Gamma[29/90] -> (
  5^(5/18) Sqrt[Pi] (-1 + 2 Cos[Pi/45]) Csc[(2 Pi)/9] Gamma[
    1/9] Gamma[7/45] Gamma[8/45])/(
  2^(29/45) 3^(1/6) Gamma[2/45] Gamma[11/45] Gamma[1/3]), 
 Gamma[31/90] -> (
  2 2^(14/45) 3^(4/15) 5^(5/18) Sqrt[Pi]
    Cos[(13 Pi)/90] Cos[(17 Pi)/90] Csc[(2 Pi)/9] Gamma[1/
    15] Gamma[1/9] Gamma[7/45]^2 Tan[(7 Pi)/45])/(
  Gamma[1/45] Gamma[2/45] Gamma[11/45] Gamma[1/3]), 
 Gamma[37/90] -> (Sqrt[Pi] Gamma[4/45] Sec[(4 Pi)/45])/(
  2^(37/45) Gamma[8/45]), 
 Gamma[41/90] -> (Sqrt[Pi] Gamma[2/45] Sec[(2 Pi)/45])/(
  2^(41/45) Gamma[4/45]), 
 Gamma[43/90] -> (Sqrt[Pi] Gamma[1/45] Sec[Pi/45])/(
  2^(43/45) Gamma[2/45]), 
 Gamma[32/91] -> (Gamma[1/91] Gamma[2/91] Gamma[3/91] Gamma[8/
      91] Gamma[9/91] Gamma[15/91] Gamma[16/91] Gamma[22/91] Gamma[4/
      13] Gamma[29/91] Gamma[5/13] Gamma[6/13] Sqrt[
     Cos[Pi/26] Cos[(3 Pi)/26] Cos[(33 Pi)/182] Cos[(
       5 Pi)/26] Csc[(4 Pi)/91] Csc[(5 Pi)/91] Csc[(6 Pi)/
       91] Csc[(11 Pi)/91] Csc[(12 Pi)/91] Csc[Pi/7] Csc[(
       18 Pi)/91] Csc[(19 Pi)/91] Sec[Pi/14] Sec[(27 Pi)/
       182] Sec[(3 Pi)/14] Sec[(41 Pi)/182] Sin[Pi/91] Sin[(
       2 Pi)/91] Sin[(3 Pi)/91] Sin[(8 Pi)/91] Sin[(9 Pi)/
       91] Sin[(15 Pi)/91] Sin[(16 Pi)/91] Sin[(22 Pi)/
       91]])/(7^(9/26) 13^(9/28)
      Gamma[4/91] Gamma[5/91] Gamma[6/91] Gamma[11/91] Gamma[12/
      91] Gamma[1/7] Gamma[18/91] Gamma[19/91] Gamma[25/91] Gamma[2/
      7] Gamma[3/7]), 
 Gamma[36/91] -> (
  Csc[(10 Pi)/91] Gamma[3/91] Gamma[16/91] Gamma[29/91] Gamma[6/
    13] Sec[(19 Pi)/182] Sec[(45 Pi)/182])/(
  8 7^(7/26) Gamma[10/91] Gamma[3/13] Gamma[23/91]), 
 Gamma[37/91] -> (
  Cos[(33 Pi)/182] Cos[(5 Pi)/26] Csc[(4 Pi)/91] Csc[(
    10 Pi)/91] Csc[(11 Pi)/91] Csc[Pi/7] Csc[(17 Pi)/
    91] Gamma[1/91] Gamma[2/91] Gamma[3/91] Gamma[8/91] Gamma[9/
    91] Gamma[15/91]^2 Gamma[16/91] Gamma[22/91]^2 Gamma[4/
    13]^2 Gamma[29/91]^2 Gamma[5/13] Gamma[6/13] Sec[(17 Pi)/
    182] Sec[(31 Pi)/182] Sec[(43 Pi)/182] Sec[(45 Pi)/
    182] Sin[Pi/91] Sin[(8 Pi)/91] Sin[(15 Pi)/91] Sin[(
    22 Pi)/91])/(
  8 7^(11/26) 13^(5/14)
    Gamma[4/91] Gamma[6/91] Gamma[10/91] Gamma[11/91] Gamma[1/
    7]^2 Gamma[2/13] Gamma[17/91] Gamma[20/91] Gamma[3/13] Gamma[23/
    91] Gamma[24/91] Gamma[27/91] Gamma[30/91] Gamma[34/91]), 
 Gamma[38/91] -> (Cos[(3 Pi)/26] Cos[(33 Pi)/182] Cos[(5 Pi)/
      26] Csc[(4 Pi)/91] Csc[(5 Pi)/91] Csc[(10 Pi)/91] Csc[(
      11 Pi)/91] Csc[(12 Pi)/91] Csc[Pi/7] Csc[(17 Pi)/
      91] Csc[(18 Pi)/91] Gamma[1/91]^2 Gamma[2/91]^2 Gamma[3/
      91] Gamma[8/91]^2 Gamma[9/91]^2 Gamma[15/91]^2 Gamma[16/
      91]^2 Gamma[22/91]^2 Gamma[4/13]^2 Gamma[29/91]^2 Gamma[5/
      13]^2 Gamma[6/13] Sec[(15 Pi)/182] Sec[(29 Pi)/182] Sec[(
      3 Pi)/14] Sec[(41 Pi)/182] Sec[(43 Pi)/182] Sin[Pi/
      91] Sin[(2 Pi)/91] Sin[(8 Pi)/91] Sin[(9 Pi)/91] Sin[(
      15 Pi)/91] Sin[(16 Pi)/91] Sin[(22 Pi)/91])/(8 7^(
     19/26) 13^(4/7)
      Gamma[4/91] Gamma[5/91]^2 Gamma[6/91] Gamma[1/13] Gamma[10/
      91] Gamma[11/91] Gamma[12/91]^2 Gamma[1/7]^2 Gamma[17/91] Gamma[
      18/91] Gamma[19/91] Gamma[20/91] Gamma[24/91] Gamma[25/
      91] Gamma[2/7]^2 Gamma[31/91] Gamma[33/91]), 
 Gamma[40/91] -> (Cos[(3 Pi)/26] Cos[(33 Pi)/182] Cos[(5 Pi)/
      26] Csc[(4 Pi)/91] Csc[(5 Pi)/91] Csc[(10 Pi)/91] Csc[(
      11 Pi)/91] Csc[Pi/7] Csc[(17 Pi)/91] Csc[(18 Pi)/
      91] Gamma[1/91] Gamma[2/91]^2 Gamma[3/91] Gamma[8/91]^2 Gamma[9/
      91]^2 Gamma[15/91]^2 Gamma[16/91]^2 Gamma[22/91]^2 Gamma[4/
      13]^2 Gamma[29/91]^2 Gamma[5/13]^2 Gamma[6/13] Sec[(29 Pi)/
      182] Sec[(3 Pi)/14] Sec[(43 Pi)/182] Sin[Pi/91] Sin[(
      2 Pi)/91] Sin[(8 Pi)/91] Sin[(9 Pi)/91] Sin[(15 Pi)/
      91] Sin[(16 Pi)/91] Sin[(22 Pi)/91])/(7^(4/13) 13^(4/7)
      Gamma[4/91] Gamma[5/91]^2 Gamma[6/91] Gamma[10/91] Gamma[11/
      91] Gamma[12/91] Gamma[1/7]^2 Gamma[2/13] Gamma[17/91] Gamma[18/
      91] Gamma[19/91] Gamma[20/91] Gamma[24/91] Gamma[2/7]^2 Gamma[
      27/91] Gamma[31/91] Gamma[33/91]), 
 Gamma[41/91] -> (
  Cos[(33 Pi)/182] Cos[(5 Pi)/26] Csc[(4 Pi)/91] Csc[(
    10 Pi)/91] Csc[Pi/7] Csc[(17 Pi)/91] Gamma[1/91] Gamma[3/
    91] Gamma[8/91] Gamma[9/91] Gamma[15/91] Gamma[16/91] Gamma[22/
    91]^2 Gamma[4/13] Gamma[29/91]^2 Gamma[5/13] Gamma[6/13] Sec[(
    31 Pi)/182] Sec[(45 Pi)/182] Sin[Pi/91] Sin[(8 Pi)/
    91] Sin[(15 Pi)/91] Sin[(22 Pi)/91])/(
  7^(1/13) 13^(5/14)
    Gamma[4/91] Gamma[6/91] Gamma[10/91] Gamma[1/7]^2 Gamma[17/
    91] Gamma[20/91] Gamma[3/13] Gamma[23/91] Gamma[27/91] Gamma[30/
    91] Gamma[34/91]), 
 Gamma[43/91] -> (
  7^(5/26) Cos[(5 Pi)/26] Csc[(4 Pi)/91] Csc[(17 Pi)/
    91] Gamma[9/91] Gamma[22/91] Gamma[4/13] Gamma[5/13] Sec[(
    5 Pi)/182] Sec[(31 Pi)/182])/(
  8 Gamma[4/91] Gamma[17/91] Gamma[30/91]), 
 Gamma[44/91] -> (
  7^(3/26) Cos[(3 Pi)/26] Csc[(5 Pi)/91] Csc[(18 Pi)/
    91] Gamma[8/91] Gamma[3/13] Gamma[34/91] Gamma[5/13] Sec[(
    3 Pi)/182] Sec[(29 Pi)/182])/(
  8 Gamma[5/91] Gamma[18/91] Gamma[31/91]), 
 Gamma[45/91] -> (7^(5/13) 13^(9/28)
      Gamma[4/91] Gamma[5/91] Gamma[1/13] Gamma[11/91] Gamma[12/
      91] Gamma[1/7] Gamma[18/91] Gamma[20/91] Gamma[25/91] Gamma[2/
      7] Gamma[33/91] Gamma[3/7] Sec[Pi/182] Sqrt[
     Cos[Pi/26] Cos[Pi/14] Cos[(3 Pi)/14] Cos[(41 Pi)/
       182] Csc[Pi/91] Csc[(2 Pi)/91] Csc[(3 Pi)/91] Csc[(
       6 Pi)/91] Csc[(8 Pi)/91] Csc[(9 Pi)/91] Csc[(
       15 Pi)/91] Csc[(16 Pi)/91] Csc[(19 Pi)/91] Csc[(
       22 Pi)/91] Sec[(3 Pi)/26] Sec[(27 Pi)/182] Sec[(
       33 Pi)/182] Sec[(5 Pi)/26] Sin[(4 Pi)/91] Sin[(
       5 Pi)/91] Sin[(11 Pi)/91] Sin[(12 Pi)/91] Sin[Pi/
       7] Sin[(18 Pi)/91]])/(8 Gamma[1/91] Gamma[2/91] Gamma[3/
      91] Gamma[8/91] Gamma[9/91] Gamma[15/91] Gamma[16/91] Gamma[22/
      91] Gamma[4/13] Gamma[29/91] Gamma[5/13]), 
 Gamma[21/92] -> (
  23^(1/8) Gamma[3/92] Gamma[1/23] Gamma[7/92] Gamma[11/92] Gamma[15/
    92] Gamma[19/92] Gamma[5/23] Gamma[1/4] Gamma[9/23] Sqrt[
   Cos[(5 Pi)/46] Csc[Pi/92] Csc[(5 Pi)/92] Csc[(2 Pi)/
     23] Csc[(9 Pi)/92] Csc[(13 Pi)/92] Csc[(17 Pi)/92] Csc[(
     21 Pi)/92] Sec[(3 Pi)/46] Sec[(11 Pi)/46] Sin[(3 Pi)/
     92] Sin[Pi/23] Sin[(7 Pi)/92] Sin[(11 Pi)/92] Sin[(
     15 Pi)/92] Sin[(19 Pi)/92] Sin[(5 Pi)/23]])/(
  2^(5/46) Gamma[1/92] Gamma[5/92] Gamma[2/23] Gamma[9/92] Gamma[13/
    92] Gamma[17/92] Gamma[6/23] Gamma[10/23]), 
 Gamma[25/92] -> (
  23^(1/8) Gamma[3/92] Gamma[7/92] Gamma[11/92] Gamma[15/92] Gamma[19/
    92] Gamma[5/23] Gamma[1/4] Gamma[9/23] Sec[(21 Pi)/92] Sqrt[
   Cos[(5 Pi)/46] Csc[Pi/92] Csc[Pi/23] Csc[(5 Pi)/
     92] Csc[(9 Pi)/92] Csc[(13 Pi)/92] Csc[(17 Pi)/92] Csc[(
     21 Pi)/92] Sec[(3 Pi)/46] Sec[(11 Pi)/46] Sin[(3 Pi)/
     92] Sin[(7 Pi)/92] Sin[(2 Pi)/23] Sin[(11 Pi)/92] Sin[(
     15 Pi)/92] Sin[(19 Pi)/92] Sin[(5 Pi)/23]])/(
  2^(17/23) Gamma[1/92] Gamma[5/92] Gamma[9/92] Gamma[13/92] Gamma[17/
    92] Gamma[6/23] Gamma[10/23]), 
 Gamma[27/92] -> (
  2 2^(11/46) Gamma[4/23] Gamma[19/92] Sin[(19 Pi)/92])/
  Gamma[2/23], 
 Gamma[29/92] -> (
  2 2^(5/46) Gamma[17/92] Gamma[6/23] Sin[(17 Pi)/92])/Gamma[3/23],
  Gamma[31/92] -> (
  2^(45/46) Gamma[15/92] Gamma[8/23] Sin[(15 Pi)/92])/Gamma[4/23], 
 Gamma[33/92] -> (
  2^(39/46) Gamma[13/92] Gamma[10/23] Sin[(13 Pi)/92])/Gamma[5/23],
  Gamma[35/92] -> (
  2^(33/46) Pi Gamma[11/92] Sec[Pi/46] Sin[(11 Pi)/92])/(
  Gamma[6/23] Gamma[11/23]), 
 Gamma[37/92] -> (Pi Gamma[9/92] Sec[(9 Pi)/92] Sec[(9 Pi)/
    46])/(2 2^(19/46) Gamma[7/23] Gamma[9/23]), 
 Gamma[39/92] -> (
  2^(21/46) Pi Gamma[7/92] Sec[(9 Pi)/46] Sin[(7 Pi)/92])/(
  Gamma[7/23] Gamma[8/23]), 
 Gamma[41/92] -> (
  2^(15/46) Pi Csc[(5 Pi)/23] Gamma[5/92] Sin[(5 Pi)/92])/(
  Gamma[5/23] Gamma[9/23]), 
 Gamma[43/92] -> (
  2^(9/46) Pi Csc[(3 Pi)/23] Gamma[3/92] Sin[(3 Pi)/92])/(
  Gamma[3/23] Gamma[10/23]), 
 Gamma[45/92] -> (
  2^(3/46) Pi Csc[Pi/23] Gamma[1/92] Sin[Pi/92])/(
  Gamma[1/23] Gamma[11/23]), 
 Gamma[17/93] -> (Csc[(17 Pi)/93] Gamma[14/93] Gamma[15/31])/(
  2 3^(3/62) Gamma[14/31]), 
 Gamma[20/93] -> (Csc[(20 Pi)/93] Gamma[11/93] Gamma[14/31])/(
  2 3^(9/62) Gamma[11/31]), 
 Gamma[23/93] -> (Csc[(23 Pi)/93] Gamma[8/93] Gamma[13/31])/(
  2 3^(15/62) Gamma[8/31]), 
 Gamma[26/93] -> (Gamma[5/93] Gamma[12/31] Sec[(41 Pi)/186])/(
  2 3^(21/62) Gamma[5/31]), 
 Gamma[28/93] -> (31^(1/12)
      Gamma[2/93] Gamma[1/31] Gamma[5/93] Gamma[8/93] Gamma[11/
      93] Gamma[4/31] Gamma[14/93] Gamma[7/31] Gamma[10/31] Gamma[13/
      31] Sqrt[
     Cos[(5 Pi)/62] Cos[(11 Pi)/62] Csc[Pi/93] Csc[(4 Pi)/
       93] Csc[(7 Pi)/93] Csc[(10 Pi)/93] Csc[(13 Pi)/
       93] Csc[(16 Pi)/93] Csc[(19 Pi)/93] Csc[(22 Pi)/
       93] Sec[(37 Pi)/186] Sec[(43 Pi)/186] Sin[(2 Pi)/
       93] Sin[Pi/31] Sin[(5 Pi)/93] Sin[(8 Pi)/93] Sin[(
       11 Pi)/93] Sin[(4 Pi)/31] Sin[(14 Pi)/93] Sin[(
       7 Pi)/31]])/(3^(55/124)
      Gamma[1/93] Gamma[4/93] Gamma[7/93] Gamma[10/93] Gamma[13/
      93] Gamma[16/93] Gamma[19/93] Gamma[22/93] Gamma[25/93]), 
 Gamma[29/93] -> (Gamma[2/93] Gamma[11/31] Sec[(35 Pi)/186])/(
  2 3^(27/62) Gamma[2/31]), 
 Gamma[32/93] -> (
  2 3^(29/62) Gamma[1/31] Gamma[10/31] Sin[Pi/31])/(
  Gamma[1/93] - 2 Gamma[1/93] Sin[(9 Pi)/62]), 
 Gamma[34/93] -> (2 31^(1/12)
      Gamma[2/93] Gamma[5/93] Gamma[8/93] Gamma[3/31] Gamma[11/
      93] Gamma[4/31] Gamma[14/93] Gamma[7/31] Gamma[10/31] Gamma[13/
      31] Sqrt[
     Cos[(5 Pi)/62] Cos[(11 Pi)/62] Cos[(37 Pi)/
       186] Csc[Pi/93] Csc[(4 Pi)/93] Csc[(7 Pi)/93] Csc[(
       10 Pi)/93] Csc[(13 Pi)/93] Csc[(16 Pi)/93] Csc[(
       19 Pi)/93] Csc[(22 Pi)/93] Sec[(43 Pi)/186] Sin[(
       2 Pi)/93] Sin[Pi/31] Sin[(5 Pi)/93] Sin[(8 Pi)/
       93] Sin[(11 Pi)/93] Sin[(4 Pi)/31] Sin[(14 Pi)/
       93] Sin[(7 Pi)/31]])/(3^(5/124)
      Gamma[1/93] Gamma[4/93] Gamma[7/93] Gamma[10/93] Gamma[13/
      93] Gamma[16/93] Gamma[19/93] Gamma[22/93] Gamma[25/93]), 
 Gamma[35/93] -> (
  2 3^(23/62) Gamma[4/31] Gamma[9/31] Sin[(4 Pi)/31])/(
  Gamma[4/93] - 2 Gamma[4/93] Sin[(5 Pi)/62]), 
 Gamma[37/93] -> (
  2 3^(19/62) Cos[(43 Pi)/186] Gamma[6/31] Gamma[25/93])/
  Gamma[2/31], 
 Gamma[38/93] -> (
  2 3^(17/62) Gamma[7/31] Gamma[8/31] Sin[(7 Pi)/31])/(
  Gamma[7/93] - 2 Gamma[7/93] Sin[Pi/62]), 
 Gamma[40/93] -> (
  2 3^(13/62) Gamma[22/93] Gamma[9/31] Sin[(22 Pi)/93])/
  Gamma[3/31], 
 Gamma[41/93] -> (
  2 3^(11/62) Cos[(11 Pi)/62] Gamma[7/31] Gamma[10/31])/(
  Gamma[10/93] + 2 Gamma[10/93] Sin[(3 Pi)/62]), 
 Gamma[43/93] -> (
  2 3^(7/62) Gamma[19/93] Gamma[12/31] Sin[(19 Pi)/93])/
  Gamma[4/31], 
 Gamma[44/93] -> (
  2 3^(5/62) Cos[(5 Pi)/62] Gamma[6/31] Gamma[13/31])/(
  Gamma[13/93] + 2 Gamma[13/93] Sin[(7 Pi)/62]), 
 Gamma[46/93] -> (
  2 3^(1/62) Gamma[16/93] Gamma[15/31] Sin[(16 Pi)/93])/
  Gamma[5/31], 
 Gamma[31/95] -> (
  Csc[(12 Pi)/95] Gamma[7/95] Gamma[26/95] Gamma[9/19] Sec[(
    33 Pi)/190])/(4 5^(5/38) Gamma[12/95] Gamma[7/19]), 
 Gamma[33/95] -> (2 Gamma[1/95] Gamma[2/95] Gamma[6/95] Gamma[7/
      95] Gamma[11/95] Gamma[3/19] Gamma[16/95] Gamma[4/19] Gamma[21/
      95] Gamma[26/95] Gamma[8/19] Gamma[9/19] Sqrt[
     Cos[Pi/38] Cos[(3 Pi)/38] Cos[(43 Pi)/190] Csc[(
       3 Pi)/95] Csc[(4 Pi)/95] Csc[(8 Pi)/95] Csc[(9 Pi)/
       95] Csc[(13 Pi)/95] Csc[(14 Pi)/95] Csc[(18 Pi)/
       95] Csc[(23 Pi)/95] Sec[(29 Pi)/190] Sec[(39 Pi)/
       190] Sin[Pi/95] Sin[(2 Pi)/95] Sin[(6 Pi)/95] Sin[(
       7 Pi)/95] Sin[(11 Pi)/95] Sin[(3 Pi)/19] Sin[(
       16 Pi)/95] Sin[(4 Pi)/19] Sin[(21 Pi)/95]])/(5^(11/19)
      19^(1/5)
      Gamma[3/95] Gamma[4/95] Gamma[8/95] Gamma[9/95] Gamma[13/
      95] Gamma[14/95] Gamma[18/95] Gamma[1/5] Gamma[23/95] Gamma[28/
      95] Gamma[2/5]), 
 Gamma[36/95] -> (
  Csc[(17 Pi)/95] Gamma[2/95] Gamma[21/95] Gamma[8/19] Sec[(
    23 Pi)/190])/(4 5^(15/38) Gamma[2/19] Gamma[17/95]), 
 Gamma[37/95] -> (Cos[(3 Pi)/38] Cos[(43 Pi)/190] Csc[(3 Pi)/
      95] Csc[(8 Pi)/95] Csc[(12 Pi)/95] Csc[(13 Pi)/
      95] Csc[(17 Pi)/95] Csc[(18 Pi)/95] Csc[(22 Pi)/
      95] Gamma[1/95]^2 Gamma[2/95] Gamma[6/95]^2 Gamma[7/95] Gamma[
      11/95]^2 Gamma[3/19] Gamma[16/95]^2 Gamma[4/19] Gamma[21/
      95]^2 Gamma[5/19] Gamma[26/95]^2 Gamma[8/19]^2 Gamma[9/19] Sec[(
      21 Pi)/190] Sec[(31 Pi)/190] Sec[(41 Pi)/
      190] Sin[Pi/95] Sin[(6 Pi)/95] Sin[(11 Pi)/95] Sin[(
      3 Pi)/19] Sin[(16 Pi)/95] Sin[(21 Pi)/95])/(2 5^(14/19)
      19^(3/10) Sqrt[10 - 2 Sqrt[5]]
      Gamma[3/95] Gamma[4/95] Gamma[1/19] Gamma[8/95] Gamma[9/
      95] Gamma[2/19] Gamma[12/95] Gamma[13/95] Gamma[14/95] Gamma[17/
      95] Gamma[18/95] Gamma[1/5]^2 Gamma[22/95] Gamma[24/95] Gamma[
      27/95] Gamma[29/95] Gamma[32/95] Gamma[34/95]), 
 Gamma[39/95] -> (Sqrt[2]
      Cos[(3 Pi)/38] Cos[(43 Pi)/190] Csc[(3 Pi)/95] Csc[(
      8 Pi)/95] Csc[(12 Pi)/95] Csc[(13 Pi)/95] Csc[(
      17 Pi)/95] Csc[(22 Pi)/95] Gamma[1/95] Gamma[2/95] Gamma[
      6/95]^2 Gamma[7/95] Gamma[11/95]^2 Gamma[3/19] Gamma[16/
      95]^2 Gamma[21/95]^2 Gamma[5/19] Gamma[26/95]^2 Gamma[8/
      19]^2 Gamma[9/19] Sec[(31 Pi)/190] Sec[(41 Pi)/
      190] Sin[Pi/95] Sin[(6 Pi)/95] Sin[(11 Pi)/95] Sin[(
      3 Pi)/19] Sin[(16 Pi)/95] Sin[(21 Pi)/95])/(5^(11/38)
      19^(3/10) Sqrt[5 - Sqrt[5]]
      Gamma[3/95] Gamma[4/95] Gamma[8/95] Gamma[9/95] Gamma[2/
      19] Gamma[12/95] Gamma[13/95] Gamma[14/95] Gamma[17/95] Gamma[1/
      5]^2 Gamma[22/95] Gamma[24/95] Gamma[27/95] Gamma[29/95] Gamma[
      32/95] Gamma[34/95]), 
 Gamma[41/95] -> (
  5^(13/38) Csc[(3 Pi)/95] Csc[(22 Pi)/95] Gamma[3/19] Gamma[16/
    95] Gamma[7/19] Sec[(13 Pi)/190] Sin[(3 Pi)/19])/(
  4 Gamma[3/95] Gamma[22/95]), 
 Gamma[42/95] -> (
  5^(11/38) Csc[(4 Pi)/95] Csc[(23 Pi)/95] Gamma[3/19] Gamma[4/
    19] Gamma[34/95] Sec[(11 Pi)/190] Sin[(4 Pi)/19])/(
  4 Gamma[4/95] Gamma[23/95]), 
 Gamma[43/95] -> (8 Gamma[1/95] Gamma[2/95] Gamma[6/95] Gamma[7/
      95] Gamma[11/95] Gamma[3/19] Gamma[16/95] Gamma[4/19] Gamma[21/
      95] Gamma[5/19] Gamma[26/95] Gamma[8/19] Gamma[9/19] Sqrt[
     Cos[Pi/38] Cos[(3 Pi)/38] Cos[(29 Pi)/190] Cos[(
       43 Pi)/190] Csc[(3 Pi)/95] Csc[(4 Pi)/95] Csc[(
       8 Pi)/95] Csc[(9 Pi)/95] Csc[(13 Pi)/95] Csc[(
       18 Pi)/95] Csc[(23 Pi)/95] Sec[(39 Pi)/190] Sin[Pi/
       95] Sin[(2 Pi)/95] Sin[(6 Pi)/95] Sin[(7 Pi)/95] Sin[(
       11 Pi)/95] Sin[(14 Pi)/95] Sin[(3 Pi)/19] Sin[(
       16 Pi)/95] Sin[(4 Pi)/19] Sin[(21 Pi)/95]])/(5^(13/38)
      19^(1/5)
      Gamma[3/95] Gamma[4/95] Gamma[1/19] Gamma[8/95] Gamma[9/
      95] Gamma[13/95] Gamma[18/95] Gamma[1/5] Gamma[23/95] Gamma[24/
      95] Gamma[28/95] Gamma[2/5]), 
 Gamma[44/95] -> (
  4 5^(7/38)
    Cos[(31 Pi)/190] Gamma[13/95] Gamma[6/19] Gamma[32/95] Sin[(
    13 Pi)/95])/(Gamma[6/95] Gamma[5/19]), 
 Gamma[46/95] -> (
  5^(3/38) Cos[(3 Pi)/38] Csc[(8 Pi)/95] Gamma[11/95] Gamma[6/
    19] Gamma[8/19] Sec[(3 Pi)/190] Sec[(41 Pi)/190])/(
  4 Gamma[8/95] Gamma[27/95]), 
 Gamma[47/95] -> (
  5^(1/38) Cos[Pi/38] Csc[(9 Pi)/95] Gamma[2/19] Gamma[29/
    95] Gamma[9/19] Sec[Pi/190] Sec[(39 Pi)/190])/(
  4 Gamma[9/95] Gamma[28/95]), 
 Gamma[19/96] -> (
  2^(7/8) Gamma[1/32] Gamma[13/96] Gamma[3/16] Sin[(13 Pi)/96])/(
  3^(3/32) Gamma[1/16] Gamma[3/32]), 
 Gamma[25/96] -> (
  2^(3/16) Sqrt[Pi]
    Csc[(7 Pi)/32] Gamma[7/96] Gamma[3/32] Sin[(7 Pi)/96])/(
  3^(9/32) Gamma[3/16] Gamma[7/32]), 
 Gamma[29/96] -> (
  4 2^(7/16) Pi Cos[Pi/32] Cos[(3 Pi)/16] Gamma[1/96] Gamma[
    7/96] Gamma[1/8] Gamma[13/96] Gamma[5/32]^2 Sec[Pi/
    8] Sin[Pi/96] Sin[(7 Pi)/96] Sin[(13 Pi)/96] Sqrt[
   Cot[(17 Pi)/96] Cot[(23 Pi)/96] Csc[(5 Pi)/96] Csc[Pi/
     16] Csc[(11 Pi)/96] Csc[(7 Pi)/32] Sin[(5 Pi)/32] Tan[(
     19 Pi)/96]])/(
  3^(3/4) Gamma[5/96] Gamma[11/96] Gamma[17/96] Gamma[3/16] Gamma[23/
    96] Gamma[1/4] Gamma[1/3]), 
 Gamma[31/96] -> (
  Sqrt[Pi]
    Csc[Pi/32] Csc[(3 Pi)/16] Gamma[1/96] Gamma[1/8] Gamma[5/
    32] Sin[Pi/96])/(
  2^(13/16) 3^(15/32) Gamma[1/32] Gamma[3/16] Gamma[1/4]), 
 Gamma[35/96] -> (
  8 2^(7/16) Pi Cos[Pi/32] Cos[(3 Pi)/16] Gamma[1/96] Gamma[
    7/96] Gamma[3/32] Gamma[1/8] Gamma[13/96] Gamma[5/32]^2 Sec[Pi/
    8] Sin[Pi/96] Sin[(7 Pi)/96] Sin[(13 Pi)/96] Sqrt[
   Cos[(19 Pi)/96] Cot[(17 Pi)/96] Cot[(23 Pi)/96] Csc[(
     5 Pi)/96] Csc[Pi/16] Csc[(11 Pi)/96] Csc[(7 Pi)/
     32] Sin[(5 Pi)/32] Sin[(19 Pi)/96]])/(
  3^(11/32) Gamma[1/32] Gamma[5/96] Gamma[11/96] Gamma[17/96] Gamma[3/
    16] Gamma[23/96] Gamma[1/4] Gamma[1/3]), 
 Gamma[37/96] -> (
  2^(5/16) 3^(11/32)
    Csc[(5 Pi)/96] Gamma[1/8] Gamma[5/32] Gamma[7/32] Sec[(
    11 Pi)/96] Sin[(5 Pi)/32] Sin[(7 Pi)/32])/(
  Gamma[5/96] Gamma[1/16]), 
 Gamma[41/96] -> (
  4 2^(5/16) 3^(7/32)
    Gamma[1/8] Gamma[7/32] Gamma[23/96] Sin[(7 Pi)/32] Sin[(
    23 Pi)/96])/(Gamma[1/16] Gamma[3/32]), 
 Gamma[43/96] -> (
  3^(5/32) Sqrt[Pi]
    Cos[(3 Pi)/16] Csc[(11 Pi)/96] Gamma[1/8] Gamma[5/32] Gamma[
    7/32] Sec[(5 Pi)/96] Sec[Pi/8])/(
  2 2^(13/16) Gamma[11/96] Gamma[3/16] Gamma[1/4]), 
 Gamma[47/96] -> (
  2^(1/16) 3^(1/32) Sqrt[Pi]
    Gamma[1/32] Gamma[17/96] Sec[Pi/32] Sin[(17 Pi)/96])/(
  Gamma[1/16] Gamma[5/32]), 
 Gamma[35/99] -> (
  Gamma[1/99] Gamma[5/99] Gamma[7/99] Gamma[14/99] Gamma[16/99] Gamma[
    23/99] Gamma[25/99] Gamma[34/99] Gamma[4/11] Sqrt[
   Cos[(3 Pi)/22] Cos[(31 Pi)/198] Cos[(49 Pi)/198] Csc[(
     2 Pi)/99] Csc[(4 Pi)/99] Csc[(8 Pi)/99] Csc[Pi/
     9] Csc[(13 Pi)/99] Csc[(17 Pi)/99] Sec[Pi/22] Sec[(
     29 Pi)/198] Sec[(47 Pi)/198] Sin[Pi/99] Sin[(5 Pi)/
     99] Sin[(7 Pi)/99] Sin[(14 Pi)/99] Sin[(16 Pi)/99] Sin[(
     23 Pi)/99]])/(
  3^(1/44) 11^(1/36)
    Gamma[2/99] Gamma[4/99] Gamma[8/99] Gamma[1/9] Gamma[13/99] Gamma[
    17/99] Gamma[26/99] Gamma[5/11]), 
 Gamma[37/99] -> (11^(1/3)
      Cos[(3 Pi)/22] Cos[(31 Pi)/198] Cos[(49 Pi)/198] Csc[(
      4 Pi)/99] Csc[(8 Pi)/99] Csc[(10 Pi)/99] Csc[(
      17 Pi)/99] Csc[(2 Pi)/11] Csc[(19 Pi)/99] Gamma[1/
      99] Gamma[5/99]^2 Gamma[7/99]^2 Gamma[14/99]^2 Gamma[16/
      99]^2 Gamma[2/9] Gamma[23/99]^2 Gamma[25/99]^2 Gamma[1/3] Gamma[
      34/99]^2 Gamma[4/11]^2 Sec[Pi/22] Sec[(25 Pi)/198] Sec[(
      43 Pi)/198] Sec[(47 Pi)/198] Sin[(5 Pi)/99] Sin[(
      7 Pi)/99] Sin[(14 Pi)/99] Sin[(16 Pi)/99] Sin[(
      2 Pi)/9] Sin[(23 Pi)/99])/(2 3^(49/66)
      Gamma[2/99] Gamma[4/99]^2 Gamma[8/99] Gamma[10/99] Gamma[1/
      9]^2 Gamma[13/99] Gamma[17/99] Gamma[2/11] Gamma[19/99] Gamma[
      20/99] Gamma[26/99] Gamma[3/11] Gamma[28/99] Gamma[31/99] Gamma[
      5/11]^2), 
 Gamma[40/99] -> (
  4 11^(1/3)
    Cos[(31 Pi)/198] Cos[(49 Pi)/198] Csc[(8 Pi)/99] Csc[(
    10 Pi)/99] Csc[(17 Pi)/99] Csc[(2 Pi)/11] Csc[(19 Pi)/
    99] Gamma[1/99] Gamma[5/99]^2 Gamma[7/99] Gamma[14/99]^2 Gamma[16/
    99]^2 Gamma[2/9] Gamma[23/99]^2 Gamma[25/99]^2 Gamma[1/3] Gamma[
    34/99]^2 Gamma[4/11] Sec[(43 Pi)/198] Sin[(5 Pi)/99] Sin[(
    7 Pi)/99] Sin[(14 Pi)/99] Sin[(16 Pi)/99] Sin[(2 Pi)/
    9] Sin[(23 Pi)/99])/(
  3^(32/33) Gamma[2/99] Gamma[4/99] Gamma[8/99] Gamma[10/99] Gamma[1/
    9]^2 Gamma[13/99] Gamma[17/99] Gamma[2/11] Gamma[19/99] Gamma[20/
    99] Gamma[3/11] Gamma[28/99] Gamma[29/99] Gamma[31/99] Gamma[5/
    11]), 
 Gamma[41/99] -> (
  11^(5/18) Cos[(31 Pi)/198] Cos[(49 Pi)/198] Csc[(8 Pi)/
    99] Csc[(10 Pi)/99] Csc[(19 Pi)/99] Gamma[1/99] Gamma[7/
    99] Gamma[14/99] Gamma[16/99] Gamma[2/9] Gamma[23/99] Gamma[25/
    99]^2 Gamma[34/99]^2 Gamma[4/11] Sec[(17 Pi)/198] Sec[(
    35 Pi)/198] Sin[(7 Pi)/99] Sin[(16 Pi)/99])/(
  2 3^(8/11)
    Gamma[2/99] Gamma[8/99] Gamma[10/99] Gamma[1/9] Gamma[19/
    99] Gamma[20/99] Gamma[3/11] Gamma[29/99] Gamma[32/99] Gamma[38/
    99]), Gamma[43/99] -> (
  Csc[(10 Pi)/99] Gamma[1/99] Gamma[23/99] Gamma[34/99] Gamma[4/
    11] Sec[(13 Pi)/198] Sec[(35 Pi)/198])/(
  8 3^(15/22) Gamma[1/11] Gamma[10/99] Gamma[32/99]), 
 Gamma[46/99] -> (3^(39/44) 11^(1/36)
      Gamma[4/99] Gamma[8/99] Gamma[1/9] Gamma[17/99] Gamma[2/
      11] Gamma[20/99] Gamma[26/99] Gamma[3/11] Gamma[31/99] Gamma[5/
      11] Sec[(7 Pi)/198] Sqrt[
     Cos[Pi/22] Cos[(47 Pi)/198] Csc[Pi/99] Csc[(2 Pi)/
       99] Csc[(5 Pi)/99] Csc[(7 Pi)/99] Csc[(13 Pi)/
       99] Csc[(14 Pi)/99] Csc[(16 Pi)/99] Csc[(23 Pi)/
       99] Sec[(3 Pi)/22] Sec[(29 Pi)/198] Sec[(31 Pi)/
       198] Sec[(49 Pi)/198] Sin[(4 Pi)/99] Sin[(8 Pi)/
       99] Sin[Pi/9] Sin[(17 Pi)/99]]
      Sin[(2 Pi)/11])/(8 Gamma[1/99] Gamma[5/99] Gamma[7/99] Gamma[
      14/99] Gamma[16/99] Gamma[23/99] Gamma[25/99] Gamma[34/
      99] Gamma[4/11]), 
 Gamma[47/99] -> (
  4 11^(5/18)
    Cos[(31 Pi)/198] Cos[(49 Pi)/198] Csc[(10 Pi)/99] Gamma[
    1/99] Gamma[7/99] Gamma[16/99] Gamma[2/9] Gamma[23/99] Gamma[25/
    99] Gamma[34/99]^2 Gamma[4/11] Sec[(35 Pi)/198] Sin[(7 Pi)/
    99] Sin[(16 Pi)/99])/(
  3^(15/22) Gamma[2/99] Gamma[1/11] Gamma[10/99] Gamma[1/9] Gamma[20/
    99] Gamma[29/99] Gamma[32/99] Gamma[38/99]), 
 Gamma[49/99] -> (
  8 3^(9/22)
    Cos[(43 Pi)/198] Gamma[17/99] Gamma[2/11] Gamma[28/99] Gamma[5/
    11] Sin[(17 Pi)/99] Sin[(2 Pi)/11])/(
  Gamma[5/99] Gamma[16/99] Gamma[38/99]), 
 Gamma[23/100] -> (
  5^(7/40) (5 - Sqrt[5])^(1/4)
    Cos[(11 Pi)/50] Csc[(6 Pi)/25] Gamma[1/100] Gamma[9/
    100] Gamma[3/25] Gamma[13/100] Gamma[4/25] Gamma[17/100] Gamma[1/
    5] Gamma[21/100] Gamma[7/25] Gamma[9/25] Sqrt[(
   Csc[(3 Pi)/100] Csc[Pi/25] Csc[(7 Pi)/100] Csc[(2 Pi)/
     25] Csc[(11 Pi)/100] Csc[(7 Pi)/50] Csc[(19 Pi)/
     100] Csc[(23 Pi)/100] Sin[Pi/100] Sin[(9 Pi)/100] Sin[(
     3 Pi)/25] Sin[(13 Pi)/100] Sin[(4 Pi)/25] Sin[(
     17 Pi)/100] Sin[(21 Pi)/100])/Pi])/(
  2 2^(31/100)
    Gamma[3/100] Gamma[1/25] Gamma[7/100] Gamma[2/25] Gamma[11/
    100] Gamma[19/100] Gamma[6/25]^2), 
 Gamma[27/100] -> (16 2^(57/100) 5^(7/40)
      Cos[(3 Pi)/50] Cos[(9 Pi)/50] Cos[(11 Pi)/50] Gamma[1/
      100] Gamma[9/100] Gamma[3/25] Gamma[13/100] Gamma[4/25] Gamma[
      17/100] Gamma[1/5] Gamma[21/100] Gamma[7/25] Gamma[9/25] Sec[(
      23 Pi)/100] Sin[(3 Pi)/25] Sin[(4 Pi)/25]^(3/2)
      Sin[(9 Pi)/50] Sqrt[(
     Csc[(3 Pi)/100] Csc[Pi/25] Csc[(7 Pi)/100] Csc[(
       11 Pi)/100] Csc[(3 Pi)/25] Csc[(7 Pi)/50] Csc[(
       19 Pi)/100] Csc[(23 Pi)/100] Sin[Pi/100] Sin[(
       2 Pi)/25] Sin[(9 Pi)/100] Sin[(13 Pi)/100] Sin[(
       17 Pi)/100] Sin[(21 Pi)/100])/Pi])/((5 - Sqrt[5])^(
     1/4) Gamma[3/100] Gamma[1/25]^2 Gamma[7/100] Gamma[11/100] Gamma[
      19/100] Gamma[6/25]^2), 
 Gamma[29/100] -> (
  2 2^(13/50) Gamma[4/25] Gamma[21/100] Sin[(21 Pi)/100])/
  Gamma[2/25], 
 Gamma[31/100] -> (
  2 2^(7/50) Gamma[19/100] Gamma[6/25] Sin[(19 Pi)/100])/
  Gamma[3/25], 
 Gamma[33/100] -> (
  2 2^(1/50) Gamma[17/100] Gamma[8/25] Sin[(17 Pi)/100])/
  Gamma[4/25], 
 Gamma[37/100] -> (
  4 2^(39/50) 5^(1/10)
    Cos[(9 Pi)/50] Gamma[3/25] Gamma[13/100] Gamma[8/25] Gamma[2/
    5] Sin[(3 Pi)/25] Sin[(13 Pi)/100])/(
  Gamma[2/25] Gamma[6/25] Gamma[7/25]), 
 Gamma[39/100] -> (Pi Csc[(4 Pi)/25] Gamma[1/25] Gamma[11/
    100] Gamma[6/25] Sec[(11 Pi)/100] Sec[(7 Pi)/50] Sec[(
    11 Pi)/50])/(
  8 2^(17/50) 5^(3/10)
    Gamma[4/25] Gamma[1/5] Gamma[7/25] Gamma[9/25]), 
 Gamma[41/100] -> (
  2^(27/50) Pi Gamma[9/100] Sec[(7 Pi)/50] Sin[(9 Pi)/100])/(
  Gamma[8/25] Gamma[9/25]), 
 Gamma[43/100] -> (Pi Gamma[7/100] Sec[(7 Pi)/100] Sec[(
    7 Pi)/50])/(2 2^(29/50) Gamma[7/25] Gamma[9/25]), 
 Gamma[47/100] -> (Pi Csc[(4 Pi)/25] Gamma[3/100] Gamma[1/
    25] Gamma[6/25] Sec[(3 Pi)/100] Sec[(3 Pi)/50] Sec[(
    7 Pi)/50])/(
  8 2^(41/50) 5^(3/10)
    Gamma[3/25] Gamma[4/25] Gamma[1/5] Gamma[9/25]), 
 Gamma[49/100] -> (Pi Csc[Pi/25] Csc[(3 Pi)/25] Gamma[1/
    100] Gamma[2/25] Gamma[7/25] Sec[(9 Pi)/50] Sin[Pi/100])/(
  2 2^(47/50) 5^(1/10)
    Gamma[1/25] Gamma[3/25] Gamma[8/25] Gamma[2/5]), 
 Gamma[23/102] -> (
  2^(13/17) Gamma[1/17] Gamma[11/102] Gamma[6/17] Sin[(11 Pi)/
    102])/(3^(3/17) Gamma[2/17] Gamma[3/17]), 
 Gamma[29/102] -> (
  2^(9/17) Pi Gamma[5/102] Gamma[2/17] Sec[(7 Pi)/34] Sin[(
    5 Pi)/102])/(3^(6/17) Gamma[4/17] Gamma[5/17] Gamma[6/17]), 
 Gamma[31/102] -> (
  3^(11/34) 17^(1/6)
    Gamma[5/102] Gamma[1/17] Gamma[11/102] Gamma[2/17] Gamma[5/
    17] Gamma[1/3]^2 Gamma[7/17] Gamma[8/17] Sqrt[
   Cos[Pi/34] Cos[(3 Pi)/34] Cos[(7 Pi)/34] Csc[Pi/
     102] Csc[(7 Pi)/102] Csc[(13 Pi)/102] Csc[(19 Pi)/
     102] Csc[(4 Pi)/17] Csc[(25 Pi)/102] Sec[(10 Pi)/
     51] Sin[(5 Pi)/102] Sin[Pi/17] Sin[(11 Pi)/102] Sin[(
     2 Pi)/17]])/(
  2^(29/51) Pi Gamma[1/102] Gamma[7/102] Gamma[13/102] Gamma[19/
    102] Gamma[4/17] Gamma[25/102]), 
 Gamma[35/102] -> (
  2 2^(5/17) 3^(8/17)
    Cos[Pi/34] Gamma[1/17] Gamma[3/17] Gamma[8/17])/(
  Gamma[1/102] Gamma[6/17]), 
 Gamma[37/102] -> (
  3^(25/34) 17^(1/6)
    Gamma[5/102] Gamma[11/102] Gamma[2/17] Gamma[3/17] Gamma[5/
    17] Gamma[1/3]^2 Gamma[7/17]^2 Sec[(7 Pi)/51] Sqrt[
   Cos[Pi/34] Cos[(3 Pi)/34] Cos[(7 Pi)/34] Csc[Pi/
     102] Csc[Pi/17] Csc[(7 Pi)/102] Csc[(13 Pi)/102] Csc[(
     19 Pi)/102] Csc[(4 Pi)/17] Csc[(25 Pi)/102] Sec[(
     10 Pi)/51] Sin[(5 Pi)/102] Sin[(11 Pi)/102] Sin[(
     2 Pi)/17]] Sin[(3 Pi)/17])/(
  2 2^(35/51) Pi Gamma[1/102] Gamma[7/102] Gamma[13/102] Gamma[19/
    102] Gamma[4/17] Gamma[25/102]), 
 Gamma[41/102] -> (
  2 2^(1/17) 3^(5/17)
    Cos[(7 Pi)/34] Gamma[4/17] Gamma[5/17] Gamma[7/17])/(
  Gamma[7/102] Gamma[8/17]), 
 Gamma[43/102] -> (
  3^(4/17) Pi Csc[(3 Pi)/17] Gamma[4/17] Gamma[25/102] Sec[(
    4 Pi)/51])/(2 2^(6/17) Gamma[3/17] Gamma[7/17] Gamma[8/17]), 
 Gamma[47/102] -> (
  2^(14/17) 3^(2/17)
    Cos[(3 Pi)/34] Csc[(4 Pi)/17] Gamma[2/17] Gamma[5/17] Gamma[
    7/17] Sin[(2 Pi)/17])/(Gamma[13/102] Gamma[4/17]), 
 Gamma[49/102] -> (
  3^(1/17) Pi Gamma[1/17] Gamma[19/102] Sec[Pi/51] Sec[(
    7 Pi)/34])/(2 2^(10/17) Gamma[2/17] Gamma[5/17] Gamma[6/17]), 
 Gamma[35/104] -> (
  13^(1/4) Gamma[5/104] Gamma[7/104] Gamma[1/13] Gamma[1/8]^2 Gamma[
    15/104] Gamma[23/104] Gamma[31/104] Gamma[6/13] Sqrt[
   Cos[Pi/26] Cos[(21 Pi)/104] Csc[Pi/104] Csc[(3 Pi)/
     104] Csc[(9 Pi)/104] Csc[(11 Pi)/104] Csc[(19 Pi)/
     104] Sec[(17 Pi)/104] Sec[(5 Pi)/26] Sec[(25 Pi)/
     104] Sin[(5 Pi)/104] Sin[(7 Pi)/104] Sin[Pi/13] Sin[(
     15 Pi)/104] Sin[(23 Pi)/104] Tan[Pi/8]])/(
  2^(9/52) Gamma[1/104] Gamma[3/104] Gamma[9/104] Gamma[11/104] Gamma[
    19/104] Gamma[1/4] Gamma[27/104] Gamma[4/13]), 
 Gamma[37/104] -> (
  13^(3/8) Sqrt[Pi]
    Cos[(21 Pi)/104] Csc[Pi/104] Csc[(9 Pi)/104] Csc[(
    2 Pi)/13] Csc[(17 Pi)/104] Csc[(25 Pi)/104] Gamma[5/
    104] Gamma[7/104] Gamma[1/13] Gamma[1/8]^2 Gamma[15/104]^2 Gamma[
    23/104]^2 Gamma[3/13] Gamma[31/104]^2 Sec[(19 Pi)/104] Sin[(
    5 Pi)/104] Sin[Pi/13] Sin[(15 Pi)/104] Sin[(23 Pi)/
    104] Tan[Pi/8])/(
  2^(33/52) Gamma[1/104] Gamma[3/104] Gamma[9/104] Gamma[11/
    104] Gamma[2/13] Gamma[17/104] Gamma[21/104] Gamma[25/104] Gamma[
    1/4] Gamma[29/104] Gamma[4/13] Gamma[33/104]), 
 Gamma[41/104] -> (
  13^(3/8) Sqrt[Pi]
    Cos[(21 Pi)/104] Csc[Pi/104] Csc[(9 Pi)/104] Csc[(
    17 Pi)/104] Csc[(25 Pi)/104] Gamma[5/104] Gamma[7/
    104] Gamma[1/8]^2 Gamma[15/104] Gamma[23/104]^2 Gamma[3/13] Gamma[
    31/104]^2 Sec[(11 Pi)/104] Sec[(19 Pi)/104] Sin[(5 Pi)/
    104] Sin[(23 Pi)/104] Tan[Pi/8])/(
  4 2^(23/52)
    Gamma[1/104] Gamma[3/104] Gamma[9/104] Gamma[17/104] Gamma[21/
    104] Gamma[25/104] Gamma[1/4] Gamma[29/104] Gamma[4/13] Gamma[33/
    104]), Gamma[43/104] -> (
  13^(1/4) Csc[(2 Pi)/13] Csc[(17 Pi)/104] Gamma[5/104] Gamma[7/
    104] Gamma[1/13] Gamma[1/8]^2 Gamma[15/104] Gamma[23/104] Gamma[
    31/104] Gamma[6/13] Sec[(9 Pi)/104] Sqrt[
   Cos[Pi/26] Cos[(5 Pi)/26] Cos[(21 Pi)/104] Csc[Pi/
     104] Csc[(3 Pi)/104] Csc[(9 Pi)/104] Csc[(11 Pi)/
     104] Csc[(19 Pi)/104] Sec[(17 Pi)/104] Sec[(25 Pi)/
     104] Sin[(5 Pi)/104] Sin[(7 Pi)/104] Sin[Pi/13] Sin[(
     15 Pi)/104] Sin[(23 Pi)/104] Tan[Pi/8]])/(
  4 2^(15/52)
    Gamma[1/104] Gamma[3/104] Gamma[11/104] Gamma[2/13] Gamma[17/
    104] Gamma[19/104] Gamma[1/4] Gamma[27/104]), 
 Gamma[45/104] -> (
  2^(1/13) Gamma[7/104] Gamma[33/104] Gamma[6/
    13] (1 - Sqrt[2] Sin[(3 Pi)/26]))/(Gamma[19/104] Gamma[3/13]), 
 Gamma[47/104] -> (
  2 2^(7/26) Pi Cos[(21 Pi)/104] Gamma[5/104] Gamma[31/
    104] Sec[(3 Pi)/26] Sin[(5 Pi)/104])/(
  Gamma[21/104] Gamma[4/13] Gamma[5/13]), 
 Gamma[49/104] -> (Pi Csc[(23 Pi)/104] Gamma[3/104] Gamma[29/
    104] Sec[(3 Pi)/104] Sec[(3 Pi)/26])/(
  8 2^(1/26) Gamma[23/104] Gamma[3/13] Gamma[5/13]), 
 Gamma[51/104] -> (Pi Csc[(25 Pi)/104] Gamma[1/104] Gamma[27/
    104] Sec[Pi/104] Sec[Pi/26])/(
  8 2^(9/26) Gamma[1/13] Gamma[25/104] Gamma[6/13]), 
 Gamma[19/105] -> (
  5^(5/28) Cos[(13 Pi)/70] Csc[(2 Pi)/105] Csc[Pi/7] Csc[(
    19 Pi)/105] Csc[(23 Pi)/105] Gamma[2/35] Gamma[4/35] Gamma[
    16/105] Gamma[6/35] Gamma[11/35]^2 Gamma[3/7] Sec[(11 Pi)/
    210] Sec[(31 Pi)/210] Sqrt[
   Cos[(3 Pi)/14] Csc[(3 Pi)/35] Csc[(8 Pi)/35] Sec[(
     17 Pi)/70] Sin[Pi/35] Sin[(2 Pi)/35] Sin[(4 Pi)/35]]
    Sin[(6 Pi)/35])/(
  8 3^(3/70) 7^(1/5) (10 - 2 Sqrt[5])^(1/4)
    Gamma[3/35]^2 Gamma[8/35] Gamma[2/7]^2 Gamma[2/5]), 
 Gamma[22/105] -> (1/(
  3^(9/70) Gamma[1/35] Gamma[2/35] Gamma[11/35] Gamma[3/7]))
  16 7^(1/5) (10/(5 + Sqrt[5]))^(1/4)
    Cos[Pi/210] Cos[(31 Pi)/210] Gamma[3/35] Gamma[13/
    105] Gamma[1/7] Gamma[2/7] Gamma[2/5] Sec[Pi/70] Sin[(2 Pi)/
    105] Sin[(13 Pi)/105] Sin[(17 Pi)/
    105] Sqrt[(5 - Sqrt[5]) Cos[(11 Pi)/210] Cos[(19 Pi)/
     210] Cos[(23 Pi)/210] Cos[(29 Pi)/210] Cos[(41 Pi)/
     210] Cos[(47 Pi)/210] Cos[(17 Pi)/70] Csc[Pi/35] Csc[(
     2 Pi)/35] Csc[(3 Pi)/35] Csc[(11 Pi)/105] Csc[(4 Pi)/
     35] Csc[(8 Pi)/35] Csc[(26 Pi)/105] Sec[(13 Pi)/
     210] Sec[(17 Pi)/210] Sin[(8 Pi)/105] Sin[Pi/7] Sin[(
     23 Pi)/105]], 
 Gamma[23/105] -> (8 5^(23/42) 7^(1/4)
      Cos[Pi/30] Csc[(4 Pi)/105] Gamma[1/15]^2 Gamma[11/
      105] Gamma[4/35] Gamma[13/105] Gamma[1/7]^2 Gamma[6/35] Gamma[2/
      7] Gamma[2/5] Sin[(13 Pi)/105] Sin[Pi/7] Sqrt[(
     2 (5 - Sqrt[5]) Cos[(11 Pi)/210] Cos[(19 Pi)/210] Cos[(
       23 Pi)/210] Cos[(41 Pi)/210] Cos[(47 Pi)/210] Cos[(
       17 Pi)/70] Csc[Pi/35] Csc[Pi/21] Csc[(8 Pi)/
       105] Csc[(3 Pi)/35] Csc[(23 Pi)/105] Csc[(8 Pi)/
       35] Csc[(26 Pi)/105] Sec[(13 Pi)/210] Sec[(17 Pi)/
       210] Sec[(29 Pi)/210] Sin[(2 Pi)/35] Sin[Pi/15] Sin[(
       2 Pi)/21] Sin[(11 Pi)/105] Sin[(4 Pi)/35] Sin[(
       2 Pi)/15] Sin[(4 Pi)/21])/(5 + Sqrt[5])])/(3^(2/35)
      Gamma[2/105] Gamma[1/35] Gamma[4/105] Gamma[1/21] Gamma[8/
      105] Gamma[1/5] Gamma[8/35] Gamma[1/3] Gamma[3/7]), 
 Gamma[26/105] -> (3^(9/70) 5^(1/7)
      Cos[(13 Pi)/70] Csc[(2 Pi)/105] Csc[(13 Pi)/
      105] Csc[Pi/7] Csc[(5 Pi)/21] Gamma[4/105] Gamma[2/
      35]^2 Gamma[8/105] Gamma[2/21] Gamma[4/35] Gamma[16/105] Gamma[
      1/5]^2 Gamma[11/35]^2 Gamma[1/3] Gamma[3/7]^2 Sec[Pi/
      30] Sin[(4 Pi)/105] Sin[(16 Pi)/105] Sin[(6 Pi)/
      35] Sqrt[((5 + Sqrt[5]) Cos[(13 Pi)/210] Cos[(17 Pi)/
       210] Cos[(29 Pi)/210] Csc[Pi/15] Csc[(3 Pi)/35] Csc[(
       2 Pi)/21] Csc[(11 Pi)/105] Csc[(2 Pi)/15] Csc[(
       4 Pi)/21] Csc[(23 Pi)/105] Csc[(8 Pi)/35] Sec[(
       11 Pi)/210] Sec[(19 Pi)/210] Sec[(23 Pi)/210] Sec[(
       41 Pi)/210] Sec[(47 Pi)/210] Sec[(17 Pi)/
       70] Sin[Pi/35] Sin[Pi/21] Sin[(2 Pi)/35] Sin[(
       8 Pi)/105] Sin[(4 Pi)/35] Sin[(26 Pi)/105])/(
     2 (5 - Sqrt[5]))])/(8 7^(7/20)
      Gamma[1/15]^2 Gamma[3/35]^2 Gamma[11/105] Gamma[13/105] Gamma[1/
      7] Gamma[8/35] Gamma[2/7]^3 Gamma[2/5]^2), 
 Gamma[29/105] -> (16 7^(1/60) Cos[Pi/210]^(3/2)
      Cos[(17 Pi)/70] Csc[Pi/35] Csc[(4 Pi)/35] Csc[(
      6 Pi)/35] Gamma[1/105] Gamma[3/35]^2 Gamma[13/105] Gamma[8/
      35]^2 Gamma[2/7]^2 Gamma[2/5] Sec[Pi/70] Sec[(13 Pi)/
      210] Sec[(17 Pi)/210] Sin[(2 Pi)/105] Sin[(13 Pi)/
      105] Sin[Pi/7] Sin[(17 Pi)/
      105] Sqrt[((5 - Sqrt[5]) Cos[(11 Pi)/210] Cos[(19 Pi)/
       210] Cos[(23 Pi)/210] Cos[(31 Pi)/210] Cos[(41 Pi)/
       210] Cos[(43 Pi)/210] Csc[Pi/21] Csc[(11 Pi)/
       105] Csc[(16 Pi)/105] Sec[(3 Pi)/14] Sin[Pi/105] Sin[(
       2 Pi)/21] Sin[(4 Pi)/21] Sin[(22 Pi)/105])/(
     5 + Sqrt[5])] Sin[(23 Pi)/105] Sin[(5 Pi)/21])/(3^(31/140)
      5^(13/42)
      Gamma[2/35] Gamma[8/105] Gamma[2/21] Gamma[4/35] Gamma[6/
      35] Gamma[1/5] Gamma[11/35] Gamma[3/7] Sin[(26 Pi)/105]^(
     3/2)), Gamma[31/105] -> (
  2 Cos[Pi/210] Csc[(4 Pi)/35] Gamma[1/35] Gamma[4/105] Gamma[8/
    35] Gamma[3/7] Sec[Pi/70] Sin[(4 Pi)/105] Sin[(17 Pi)/
    105])/(3^(27/70) 5^(5/14) Gamma[4/35] Gamma[1/7] Gamma[6/35]), 
 Gamma[32/105] -> (
  Cos[(13 Pi)/70] Csc[(11 Pi)/105] Gamma[1/35] Gamma[4/
    105] Gamma[1/21] Gamma[8/35] Gamma[11/35] Gamma[3/7] Sec[(
    41 Pi)/210] Sin[(4 Pi)/105] Sqrt[
   Csc[(2 Pi)/21] Csc[Pi/7] Csc[(4 Pi)/21] Sin[Pi/21]])/(
  2 3^(67/140) 5^(13/42) 7^(1/12)
    Gamma[3/35] Gamma[11/105] Gamma[1/7] Gamma[17/105] Gamma[2/7]), 
 Gamma[34/105] -> (
  7^(1/10) Sqrt[(5 - Sqrt[5])/(5 + Sqrt[5])]
    Cos[Pi/210] Cos[(11 Pi)/210] Cos[(31 Pi)/210] Cos[(
    17 Pi)/70] Csc[Pi/35] Csc[(11 Pi)/105] Csc[(4 Pi)/
    35] Csc[(6 Pi)/35] Csc[(26 Pi)/105] Gamma[1/105] Gamma[3/
    35]^2 Gamma[8/35]^2 Gamma[2/7] Gamma[2/5] Sec[Pi/70] Sec[(
    13 Pi)/210] Sec[(17 Pi)/210] Sec[(37 Pi)/210] Sec[(
    3 Pi)/14] Sin[(2 Pi)/105] Sin[Pi/7] Sin[(17 Pi)/
    105] Sin[(23 Pi)/105])/(
  4 3^(33/70) 5^(3/7)
    Gamma[2/35] Gamma[4/35] Gamma[1/7] Gamma[6/35] Gamma[1/5] Gamma[
    11/35]), 
 Gamma[37/105] -> (
  2 3^(31/70) Gamma[2/35] Gamma[11/35] Sin[(2 Pi)/35])/(
  Gamma[2/105] - 2 Gamma[2/105] Sin[(9 Pi)/70]), 
 Gamma[38/105] -> (
  Cos[(13 Pi)/70] Csc[(11 Pi)/105] Gamma[4/105] Gamma[1/
    21] Gamma[8/35] Gamma[11/35] Gamma[3/7] Sin[(4 Pi)/105] Sqrt[
   Csc[(2 Pi)/21] Csc[Pi/7] Csc[(4 Pi)/21] Sin[Pi/21]])/(
  3^(9/140) 5^(13/42) 7^(1/12)
    Gamma[11/105] Gamma[1/7] Gamma[17/105] Gamma[2/7]), 
 Gamma[41/105] -> (32 3^(3/28) 7^(1/60) Cos[Pi/210]^(3/2)
      Cos[(47 Pi)/210] Cos[(17 Pi)/70] Csc[Pi/35] Csc[(
      4 Pi)/35] Csc[(6 Pi)/35] Gamma[1/105] Gamma[3/35]^2 Gamma[
      13/105] Gamma[8/35]^2 Gamma[2/7]^2 Gamma[2/5] Sec[Pi/
      70] Sec[(13 Pi)/210] Sec[(17 Pi)/210] Sin[(2 Pi)/
      105] Sin[(13 Pi)/105] Sin[Pi/7] Sin[(17 Pi)/
      105] Sqrt[((5 - Sqrt[5]) Cos[(11 Pi)/210] Cos[(19 Pi)/
       210] Cos[(23 Pi)/210] Cos[(31 Pi)/210] Cos[(41 Pi)/
       210] Cos[(43 Pi)/210] Csc[Pi/21] Csc[(11 Pi)/
       105] Csc[(16 Pi)/105] Sec[(3 Pi)/14] Sin[Pi/105] Sin[(
       2 Pi)/21] Sin[(4 Pi)/21] Sin[(22 Pi)/105])/(
     5 + Sqrt[5])] Sin[(23 Pi)/105] Sin[(5 Pi)/21])/(5^(13/42)
      Gamma[2/35]^2 Gamma[8/105] Gamma[2/21] Gamma[4/35] Gamma[1/
      5] Gamma[11/35] Gamma[3/7] Sin[(26 Pi)/105]^(3/2)), 
 Gamma[43/105] -> (
  3^(19/70) Csc[(6 Pi)/35] Gamma[1/35] Gamma[3/35] Gamma[8/
    35]^2 Gamma[2/7] Sqrt[
   Cos[(11 Pi)/210] Cos[(23 Pi)/210] Cos[(47 Pi)/210] Cos[(
     17 Pi)/70] Csc[Pi/35] Csc[(8 Pi)/105] Csc[(11 Pi)/
     105] Csc[(4 Pi)/35] Csc[(26 Pi)/105] Sec[(13 Pi)/
     210] Sec[(17 Pi)/210] Sec[(19 Pi)/210] Sec[(29 Pi)/
     210] Sec[(41 Pi)/210] Sin[(2 Pi)/35] Sin[(3 Pi)/
     35] Sin[Pi/7] Sin[(23 Pi)/105] Sin[(8 Pi)/35]])/(
  2 5^(3/28) 7^(1/10) (2 (5 + Sqrt[5]))^(1/4)
    Gamma[2/35] Gamma[8/105] Gamma[4/35] Gamma[1/5]), 
 Gamma[44/105] -> (3^(13/35) 5^(1/28)
      Cos[(13 Pi)/70] Csc[(2 Pi)/105] Csc[(13 Pi)/
      105] Csc[Pi/7] Csc[(5 Pi)/21] Gamma[1/35] Gamma[4/
      105] Gamma[2/35] Gamma[8/105] Gamma[2/21] Gamma[16/105] Gamma[1/
      5] Gamma[11/35]^2 Gamma[1/3] Gamma[3/7]^2 Sec[Pi/30] Sec[(
      17 Pi)/70] Sin[Pi/35] Sin[(4 Pi)/
      105] Sqrt[(5 + Sqrt[5]) Cos[(13 Pi)/210] Cos[(17 Pi)/
       210] Cos[(29 Pi)/210] Cos[(3 Pi)/14] Csc[Pi/15] Csc[(
       2 Pi)/21] Csc[(11 Pi)/105] Csc[(2 Pi)/15] Csc[(
       4 Pi)/21] Csc[(23 Pi)/105] Sec[(11 Pi)/210] Sec[(
       19 Pi)/210] Sec[(23 Pi)/210] Sec[(41 Pi)/210] Sec[(
       47 Pi)/210] Sin[Pi/21] Sin[(8 Pi)/105]]
      Sin[(16 Pi)/105] Sin[(6 Pi)/35] Sin[(26 Pi)/105]^(
     3/2))/(2 7^(9/20) (2 (5 - Sqrt[5]))^(3/4)
      Gamma[1/15]^2 Gamma[3/35]^2 Gamma[11/105] Gamma[13/105] Gamma[1/
      7] Gamma[2/7]^2 Gamma[2/5]^2), 
 Gamma[46/105] -> (
  2 3^(13/70) Cos[(13 Pi)/70] Gamma[8/35] Gamma[11/35])/(
  Gamma[11/105] + 2 Gamma[11/105] Sin[(3 Pi)/70]), 
 Gamma[47/
   105] -> (8 3^(1/10) 5^(5/42) 7^(7/20)
      Cos[Pi/30] Csc[(4 Pi)/105] Csc[(6 Pi)/35] Gamma[1/
      15]^2 Gamma[3/35]^2 Gamma[11/105] Gamma[13/105] Gamma[1/
      7] Gamma[8/35] Gamma[2/7]^2 Gamma[2/5]^2 Sec[(13 Pi)/
      70] Sin[(13 Pi)/105] Sin[Pi/7] Sqrt[(
     2 (5 - Sqrt[5]) Cos[(11 Pi)/210] Cos[(19 Pi)/210] Cos[(
       23 Pi)/210] Cos[(41 Pi)/210] Cos[(47 Pi)/210] Cos[(
       17 Pi)/70] Csc[Pi/35] Csc[Pi/21] Csc[(8 Pi)/
       105] Csc[(4 Pi)/35] Csc[(26 Pi)/105] Sec[(13 Pi)/
       210] Sec[(17 Pi)/210] Sec[(29 Pi)/210] Sin[(2 Pi)/
       35] Sin[Pi/15] Sin[(3 Pi)/35] Sin[(2 Pi)/21] Sin[(
       11 Pi)/105] Sin[(2 Pi)/15] Sin[(4 Pi)/21] Sin[(
       23 Pi)/105] Sin[(8 Pi)/35])/(
     5 + Sqrt[5])])/(Gamma[2/105] Gamma[4/105] Gamma[1/21] Gamma[2/
      35] Gamma[8/105] Gamma[4/35] Gamma[1/5]^2 Gamma[11/35] Gamma[1/
      3] Gamma[3/7]), 
 Gamma[52/105] -> (
  2 3^(1/70) 5^(1/14)
    Cos[Pi/70] Cos[(13 Pi)/70] Csc[(17 Pi)/105] Gamma[4/
    35] Gamma[6/35] Gamma[11/35] Gamma[3/7] Sec[Pi/210] Sin[(
    4 Pi)/35])/(Gamma[3/35] Gamma[17/105] Gamma[2/7]), 
 Gamma[25/108] -> (
  32 2^(13/18) 3^(11/24)
    Gamma[1/27]^2 Gamma[7/108] Gamma[11/108] Gamma[19/108] Gamma[5/
    27]^2 Gamma[23/108] Gamma[2/9] Gamma[1/4] Gamma[1/3] Sin[(
    5 Pi)/54]^2 Sin[(7 Pi)/54] Sin[(11 Pi)/54]^2 Sqrt[(
   Csc[Pi/108] Csc[Pi/27] Csc[(5 Pi)/108] Csc[(2 Pi)/
     27] Csc[(5 Pi)/54] Csc[(13 Pi)/108] Csc[(17 Pi)/
     108] Csc[(11 Pi)/54] Csc[(25 Pi)/108] Sin[Pi/54] Sin[(
     7 Pi)/108] Sin[(11 Pi)/108] Sin[Pi/9] Sin[(19 Pi)/
     108] Sin[(23 Pi)/108])/Pi]
    Sin[(2 Pi)/9] Sin[(13 Pi)/54])/(
  Gamma[1/108] Gamma[5/108] Gamma[2/27] Gamma[1/9]^2 Gamma[13/
    108] Gamma[4/27] Gamma[17/108] Gamma[8/27]), 
 Gamma[29/108] -> (
  2 2^(1/9) 3^(11/24)
    Cos[Pi/54] Gamma[1/27] Gamma[7/108] Gamma[11/108] Gamma[19/
    108] Gamma[5/27]^2 Gamma[23/108] Gamma[2/9] Gamma[1/4] Gamma[1/
    3] Sec[(11 Pi)/54] Sec[(25 Pi)/108] Sin[(5 Pi)/
    27]^2 Sqrt[(
   Cos[(5 Pi)/54] Cos[(5 Pi)/27] Csc[Pi/108] Csc[(5 Pi)/
     108] Csc[Pi/9] Csc[(13 Pi)/108] Csc[(17 Pi)/108] Csc[(
     11 Pi)/54] Csc[(25 Pi)/108] Csc[(13 Pi)/54] Sec[(
     7 Pi)/54] Sec[(13 Pi)/54] Sin[(7 Pi)/108] Sin[(2 Pi)/
     27] Sin[(11 Pi)/108] Sin[(19 Pi)/108] Sin[(23 Pi)/
     108])/Pi] Sin[(2 Pi)/9])/(
  Gamma[1/108] Gamma[5/108] Gamma[1/9]^2 Gamma[13/108] Gamma[4/
    27] Gamma[17/108] Gamma[8/27]), 
 Gamma[31/108] -> (
  2 2^(5/18) Gamma[4/27] Gamma[23/108] Sin[(23 Pi)/108])/
  Gamma[2/27], 
 Gamma[35/108] -> (
  2 2^(1/18) Gamma[19/108] Gamma[8/27] Sin[(19 Pi)/108])/
  Gamma[4/27], 
 Gamma[37/108] -> (
  3^(7/18) Csc[(5 Pi)/54] Csc[(11 Pi)/54] Gamma[1/9] Gamma[17/
    108] Gamma[8/27] Sin[(17 Pi)/108] Sin[(5 Pi)/27])/(
  2^(1/18) Gamma[1/27] Gamma[5/27]), 
 Gamma[41/108] -> (Pi Csc[Pi/27] Csc[(5 Pi)/27] Csc[(
    2 Pi)/9] Gamma[1/9] Gamma[13/108] Gamma[4/27] Sin[Pi/
    54] Sin[(13 Pi)/108])/(
  2^(5/18) 3^(2/9) Gamma[5/27] Gamma[2/9] Gamma[7/27] Gamma[1/3]), 
 Gamma[43/108] -> (Pi Gamma[2/27] Gamma[11/108] Sec[(5 Pi)/
    54] Sec[(13 Pi)/54] Sin[(11 Pi)/108])/(
  2^(7/18) 3^(5/18) Gamma[2/9] Gamma[7/27] Gamma[8/27]), 
 Gamma[47/108] -> ((2/3)^(
   7/18) Pi Gamma[1/27] Gamma[7/108] Sin[(7 Pi)/108])/(
  Gamma[1/9] Gamma[7/27] Gamma[8/27] (Cos[Pi/27] + Sin[Pi/18])),
  Gamma[49/
   108] -> (Pi Gamma[5/108] Gamma[2/27] Sec[(5 Pi)/108] Sec[(
    5 Pi)/54] Sec[(13 Pi)/54])/(
  4 2^(13/18) 3^(5/18) Gamma[5/27] Gamma[2/9] Gamma[7/27]), 
 Gamma[53/108] -> (Pi Csc[(5 Pi)/27] Csc[(2 Pi)/9] Gamma[1/
    108] Gamma[1/9] Gamma[4/27] Sec[Pi/108] Sec[Pi/54])/(
  8 2^(17/18) 3^(2/9) Gamma[1/27] Gamma[5/27] Gamma[2/9] Gamma[1/3]), 
 Gamma[39/110] -> (
  16 2^(6/11) Pi Gamma[1/110] Gamma[3/110] Gamma[1/11] Gamma[13/
    110] Gamma[23/110] Sin[(3 Pi)/110] Sin[(13 Pi)/110] Sin[(
    23 Pi)/110] Sqrt[
   Cos[Pi/55] Cos[(4 Pi)/55] Cos[(6 Pi)/55] Cos[(9 Pi)/
     55] Csc[(9 Pi)/110] Csc[(19 Pi)/110] Sec[(3 Pi)/
     22] Sec[(8 Pi)/55] Sec[(13 Pi)/55] Sin[Pi/
     110] Sin[Pi/11] Sin[(27 Pi)/110]])/(
  5^(9/22) 11^(3/10)
    Gamma[7/110] Gamma[9/110] Gamma[17/110] Gamma[19/110] Gamma[29/
    110] Gamma[4/11]), 
 Gamma[41/110] -> (
  512 2^(7/11) Pi^2 Cos[Pi/55] Cos[Pi/22] Cos[(4 Pi)/
    55] Cos[(6 Pi)/55] Csc[(2 Pi)/11] Gamma[1/110] Gamma[3/
    110]^2 Gamma[1/11] Gamma[13/110]^2 Gamma[23/110]^2 Sec[(5 Pi)/
    22] Sin[Pi/110] Sin[(3 Pi)/110]^2 Sin[(13 Pi)/
    110]^2 Sin[(23 Pi)/110]^2)/(
  5^(8/11) 11^(1/5)
    Gamma[7/110] Gamma[9/110] Gamma[17/110] Gamma[19/110] Gamma[2/
    11] Gamma[21/110] Gamma[27/110] Gamma[31/110] Gamma[37/110] Gamma[
    4/11]^2), 
 Gamma[43/110] -> (
  2 2^(3/11) Pi Csc[Pi/11] Gamma[1/110] Gamma[23/110] Sin[Pi/
    110] Sin[(23 Pi)/110])/(
  5^(5/11) Gamma[2/11] Gamma[21/110] Gamma[5/11]), 
 Gamma[47/110] -> (
  128 2^(9/11) Pi^2 Cos[Pi/55] Cos[(6 Pi)/55] Csc[(2 Pi)/
    11] Gamma[1/110] Gamma[3/110] Gamma[1/11] Gamma[13/110]^2 Gamma[
    23/110]^2 Sin[Pi/110] Sin[(3 Pi)/110] Sin[(13 Pi)/
    110]^2 Sin[(23 Pi)/110]^2)/(
  5^(4/11) 11^(1/5)
    Gamma[7/110] Gamma[9/110] Gamma[17/110] Gamma[2/11] Gamma[21/
    110] Gamma[27/110] Gamma[31/110] Gamma[37/110] Gamma[4/11] Gamma[
    5/11]), Gamma[49/110] -> (
  4 2^(2/11) Pi Cos[Pi/22] Gamma[1/110] Gamma[3/110] Gamma[13/
    110] Gamma[23/110] Gamma[3/11] Sec[(3 Pi)/55] Sqrt[
   Cos[Pi/55] Cos[(4 Pi)/55] Cos[(6 Pi)/55] Cos[(9 Pi)/
     55] Csc[(9 Pi)/110] Csc[Pi/11] Csc[(19 Pi)/110] Csc[(
     27 Pi)/110] Sec[(3 Pi)/22] Sec[(8 Pi)/55] Sec[(
     13 Pi)/55] Sin[Pi/110]]
    Sin[(3 Pi)/110] Sin[(13 Pi)/110] Sin[(23 Pi)/110])/(
  5^(3/22) 11^(3/10)
    Gamma[7/110] Gamma[9/110] Gamma[19/110] Gamma[27/110] Gamma[29/
    110] Gamma[4/11]), 
 Gamma[51/110] -> (
  4 2^(1/11) 5^(2/11)
    Cos[(9 Pi)/55] Cos[(5 Pi)/22] Gamma[2/11] Gamma[3/11] Gamma[
    37/110] Sec[(3 Pi)/22] Sin[(2 Pi)/11])/(
  Gamma[7/110] Gamma[29/110]), 
 Gamma[53/110] -> (
  2 2^(6/11) 5^(
   1/11) Pi Csc[(2 Pi)/11] Gamma[1/11] Gamma[13/110] Sin[Pi/
    11] Sin[(13 Pi)/110])/(Gamma[9/110] Gamma[31/110] Gamma[4/11]),
  Gamma[20/111] -> (Csc[(20 Pi)/111] Gamma[17/111] Gamma[18/37])/(
  2 3^(3/74) Gamma[17/37]), 
 Gamma[23/111] -> (Csc[(23 Pi)/111] Gamma[14/111] Gamma[17/37])/(
  2 3^(9/74) Gamma[14/37]), 
 Gamma[26/111] -> (Csc[(26 Pi)/111] Gamma[11/111] Gamma[16/37])/(
  2 3^(15/74) Gamma[11/37]), 
 Gamma[29/111] -> (Gamma[8/111] Gamma[15/37] Sec[(53 Pi)/222])/(
  2 3^(21/74) Gamma[8/37]), 
 Gamma[32/111] -> (Gamma[5/111] Gamma[14/37] Sec[(47 Pi)/222])/(
  2 3^(27/74) Gamma[5/37]), 
 Gamma[34/
   111] -> (37^(1/12)
      Gamma[2/111] Gamma[1/37] Gamma[5/111] Gamma[8/111] Gamma[11/
      111] Gamma[4/37] Gamma[14/111] Gamma[17/111] Gamma[7/37] Gamma[
      10/37] Gamma[13/37] Gamma[16/37] Sqrt[
     Cos[(5 Pi)/74] Cos[(11 Pi)/74] Cos[(17 Pi)/
       74] Csc[Pi/111] Csc[(4 Pi)/111] Csc[(7 Pi)/111] Csc[(
       10 Pi)/111] Csc[(13 Pi)/111] Csc[(16 Pi)/111] Csc[(
       19 Pi)/111] Csc[(22 Pi)/111] Csc[(25 Pi)/111] Sec[(
       43 Pi)/222] Sec[(49 Pi)/222] Sec[(55 Pi)/222] Sin[(
       2 Pi)/111] Sin[Pi/37] Sin[(5 Pi)/111] Sin[(8 Pi)/
       111] Sin[(11 Pi)/111] Sin[(4 Pi)/37] Sin[(14 Pi)/
       111] Sin[(17 Pi)/111] Sin[(7 Pi)/37]])/(3^(21/37)
      Gamma[1/111] Gamma[4/111] Gamma[7/111] Gamma[10/111] Gamma[13/
      111] Gamma[16/111] Gamma[19/111] Gamma[22/111] Gamma[25/
      111] Gamma[28/111] Gamma[31/111]), 
 Gamma[35/111] -> (Gamma[2/111] Gamma[13/37] Sec[(41 Pi)/222])/(
  2 3^(33/74) Gamma[2/37]), 
 Gamma[38/111] -> (
  2 3^(35/74) Gamma[1/37] Gamma[12/37] Sin[Pi/37])/(
  Gamma[1/111] - 2 Gamma[1/111] Sin[(11 Pi)/74]), 
 Gamma[40/111] -> (2 37^(1/12)
      Gamma[2/111] Gamma[5/111] Gamma[8/111] Gamma[3/37] Gamma[11/
      111] Gamma[4/37] Gamma[14/111] Gamma[17/111] Gamma[7/37] Gamma[
      10/37] Gamma[13/37] Gamma[16/37] Sqrt[
     Cos[(5 Pi)/74] Cos[(11 Pi)/74] Cos[(43 Pi)/222] Cos[(
       17 Pi)/74] Csc[Pi/111] Csc[(4 Pi)/111] Csc[(7 Pi)/
       111] Csc[(10 Pi)/111] Csc[(13 Pi)/111] Csc[(16 Pi)/
       111] Csc[(19 Pi)/111] Csc[(22 Pi)/111] Csc[(25 Pi)/
       111] Sec[(49 Pi)/222] Sec[(55 Pi)/222] Sin[(2 Pi)/
       111] Sin[Pi/37] Sin[(5 Pi)/111] Sin[(8 Pi)/111] Sin[(
       11 Pi)/111] Sin[(4 Pi)/37] Sin[(14 Pi)/111] Sin[(
       17 Pi)/111] Sin[(7 Pi)/37]])/(3^(11/74)
      Gamma[1/111] Gamma[4/111] Gamma[7/111] Gamma[10/111] Gamma[13/
      111] Gamma[16/111] Gamma[19/111] Gamma[22/111] Gamma[25/
      111] Gamma[28/111] Gamma[31/111]), 
 Gamma[41/111] -> (
  2 3^(29/74) Gamma[4/37] Gamma[11/37] Sin[(4 Pi)/37])/(
  Gamma[4/111] - 2 Gamma[4/111] Sin[(7 Pi)/74]), 
 Gamma[43/111] -> (
  2 3^(25/74) Cos[(49 Pi)/222] Gamma[6/37] Gamma[31/111])/
  Gamma[2/37], 
 Gamma[44/111] -> (
  2 3^(23/74) Gamma[7/37] Gamma[10/37] Sin[(7 Pi)/37])/(
  Gamma[7/111] - 2 Gamma[7/111] Sin[(3 Pi)/74]), 
 Gamma[46/111] -> (
  2 3^(19/74) Cos[(55 Pi)/222] Gamma[9/37] Gamma[28/111])/
  Gamma[3/37], 
 Gamma[47/111] -> (
  2 3^(17/74) Cos[(17 Pi)/74] Gamma[9/37] Gamma[10/37])/(
  Gamma[10/111] + 2 Gamma[10/111] Sin[Pi/74]), 
 Gamma[49/111] -> (
  2 3^(13/74) Gamma[25/111] Gamma[12/37] Sin[(25 Pi)/111])/
  Gamma[4/37], 
 Gamma[50/111] -> (
  2 3^(11/74) Cos[(11 Pi)/74] Gamma[8/37] Gamma[13/37])/(
  Gamma[13/111] + 2 Gamma[13/111] Sin[(5 Pi)/74]), 
 Gamma[52/111] -> (
  2 3^(7/74) Gamma[22/111] Gamma[15/37] Sin[(22 Pi)/111])/
  Gamma[5/37], 
 Gamma[53/111] -> (
  2 3^(5/74) Cos[(5 Pi)/74] Gamma[7/37] Gamma[16/37])/(
  Gamma[16/111] + 2 Gamma[16/111] Sin[(9 Pi)/74]), 
 Gamma[55/111] -> (
  2 3^(1/74) Gamma[19/111] Gamma[18/37] Sin[(19 Pi)/111])/
  Gamma[6/37], 
 Gamma[41/112] -> (Pi Gamma[1/112] Gamma[3/112] Gamma[5/112] Gamma[
    17/112] Gamma[19/112] Gamma[33/112] Sqrt[
   1/7 Cos[(23 Pi)/112] Csc[(9 Pi)/112] Csc[(11 Pi)/
     112] Csc[(13 Pi)/112] Csc[Pi/7] Csc[(25 Pi)/112] Csc[(
     27 Pi)/112] Sec[Pi/14] Sec[(15 Pi)/112] Sin[Pi/
     112] Sin[(3 Pi)/112] Sin[(5 Pi)/112] Sin[(17 Pi)/
     112] Sin[(19 Pi)/112]])/(
  2 2^(11/28)
    Gamma[9/112] Gamma[11/112] Gamma[13/112] Gamma[1/7] Gamma[25/
    112] Gamma[27/112] Gamma[3/7]), 
 Gamma[43/112] -> (Pi^(3/2)
    Cos[(23 Pi)/112] Csc[(11 Pi)/112] Csc[(13 Pi)/112] Csc[(
    15 Pi)/112] Csc[(27 Pi)/112] Gamma[1/112] Gamma[3/
    112]^2 Gamma[5/112]^2 Gamma[17/112]^2 Gamma[19/112]^2 Gamma[33/
    112]^2 Sec[Pi/16] Sec[Pi/14] Sec[(13 Pi)/112] Sec[(
    27 Pi)/112] Sin[(3 Pi)/112] Sin[(5 Pi)/112] Sin[(
    17 Pi)/112] Sin[(19 Pi)/112])/(
  8 2^(1/56) 7^(15/16)
    Gamma[9/112] Gamma[11/112]^2 Gamma[13/112] Gamma[1/8] Gamma[15/
    112] Gamma[1/7] Gamma[23/112] Gamma[25/112] Gamma[27/112] Gamma[
    29/112] Gamma[39/112] Gamma[3/7]), 
 Gamma[45/112] -> (
  Sqrt[Pi]
    Cos[Pi/8] Cos[(23 Pi)/112] Csc[(13 Pi)/112] Csc[(
    15 Pi)/112] Gamma[1/112] Gamma[3/112] Gamma[5/112] Gamma[17/
    112] Gamma[19/112]^2 Gamma[1/4] Gamma[2/7] Gamma[33/
    112]^2 Sec[Pi/16] Sec[(11 Pi)/112] Sec[(3 Pi)/16] Sec[(
    25 Pi)/112] Sec[(27 Pi)/112] Sin[(5 Pi)/112] Sin[(
    19 Pi)/112])/(
  4 2^(27/28) 7^(3/4)
    Gamma[9/112] Gamma[13/112] Gamma[1/8]^2 Gamma[15/112] Gamma[1/
    7] Gamma[23/112] Gamma[29/112] Gamma[31/112] Gamma[37/112]), 
 Gamma[47/112] -> (
  Sqrt[Pi]
    Csc[(15 Pi)/112] Gamma[1/112] Gamma[17/112] Gamma[33/
    112] Sec[Pi/16] Sec[(9 Pi)/112] Sec[(25 Pi)/112])/(
  8 2^(7/8) 7^(7/16) Gamma[1/8] Gamma[15/112] Gamma[31/112]), 
 Gamma[51/112] -> (
  Sqrt[Pi]
    Cos[(23 Pi)/112] Csc[(15 Pi)/112] Gamma[1/112] Gamma[5/
    112] Gamma[17/112] Gamma[19/112] Gamma[2/7] Gamma[33/
    112]^2 Sec[Pi/16] Sec[(25 Pi)/112] Sin[(5 Pi)/112] Sin[(
    19 Pi)/112])/(
  2^(5/56) 7^(7/16)
    Gamma[9/112] Gamma[1/8] Gamma[15/112] Gamma[1/7] Gamma[23/
    112] Gamma[31/112] Gamma[37/112]), 
 Gamma[53/112] -> (
  2^(3/28) Pi^(3/2)
    Cos[Pi/8] Cos[(23 Pi)/112] Csc[(13 Pi)/112] Csc[(
    15 Pi)/112] Gamma[1/112] Gamma[3/112]^2 Gamma[5/112] Gamma[17/
    112]^2 Gamma[19/112]^2 Gamma[1/4] Gamma[33/112]^2 Sec[Pi/
    16] Sec[Pi/14] Sec[(3 Pi)/16] Sec[(27 Pi)/112] Sin[(
    3 Pi)/112] Sin[(5 Pi)/112] Sin[(17 Pi)/112] Sin[(
    19 Pi)/112])/(
  7^(3/4) Gamma[9/112] Gamma[11/112] Gamma[13/112] Gamma[1/8]^2 Gamma[
    15/112] Gamma[1/7] Gamma[23/112] Gamma[25/112] Gamma[29/
    112] Gamma[37/112] Gamma[39/112] Gamma[3/7]), 
 Gamma[55/112] -> (
  2^(41/56) Pi^(3/2)
    Gamma[1/112] Gamma[3/112] Gamma[5/112] Gamma[17/112] Gamma[19/
    112] Gamma[33/112] Sec[Pi/16] Sqrt[
   Cos[(15 Pi)/112] Cos[(23 Pi)/112] Csc[(11 Pi)/112] Csc[(
     13 Pi)/112] Csc[Pi/7] Csc[(27 Pi)/112] Sec[Pi/
     14] Sin[Pi/112] Sin[(3 Pi)/112] Sin[(5 Pi)/112] Sin[(
     9 Pi)/112] Sin[(17 Pi)/112] Sin[(19 Pi)/112] Sin[(
     25 Pi)/112]])/(
  7^(7/16) Gamma[11/112] Gamma[13/112] Gamma[1/8] Gamma[1/7] Gamma[23/
    112] Gamma[27/112] Gamma[39/112] Gamma[3/7]), 
 Gamma[25/114] -> (
  2^(15/19) Gamma[1/19] Gamma[13/114] Gamma[6/19] Sin[(13 Pi)/
    114])/(3^(3/19) Gamma[2/19] Gamma[3/19]), 
 Gamma[31/114] -> (
  2^(11/19) Pi Gamma[7/114] Gamma[2/19] Sec[(5 Pi)/38] Sin[(
    7 Pi)/114])/(3^(6/19) Gamma[4/19] Gamma[6/19] Gamma[7/19]), 
 Gamma[35/114] -> (
  Gamma[1/114] Gamma[1/19] Gamma[7/114] Gamma[13/114] Gamma[4/
    19] Gamma[5/19] Gamma[7/
    19] Sqrt[Pi Cos[(5 Pi)/38] Cos[(9 Pi)/38] Csc[(5 Pi)/
     114] Csc[(11 Pi)/114] Csc[(2 Pi)/19] Csc[(17 Pi)/
     114] Csc[(23 Pi)/114] Sec[(3 Pi)/38] Sec[(11 Pi)/
     57] Sec[(14 Pi)/57] Sin[Pi/114] Sin[Pi/19] Sin[(
     7 Pi)/114] Sin[(13 Pi)/114] Sin[(4 Pi)/19]])/(
  2^(9/38) 3^(21/38) 19^(1/6)
    Gamma[5/114] Gamma[11/114] Gamma[2/19] Gamma[17/114] Gamma[23/
    114] Gamma[29/114] Gamma[8/19]), 
 Gamma[37/114] -> (
  2^(7/19) Pi Csc[Pi/19] Gamma[1/114] Gamma[3/19] Sin[Pi/
    114])/(3^(9/19) Gamma[1/19] Gamma[6/19] Gamma[9/19]), 
 Gamma[41/114] -> (
  Gamma[1/114] Gamma[7/114] Gamma[13/114] Gamma[3/19] Gamma[4/
    19] Gamma[5/19] Gamma[7/19] Sec[(8 Pi)/57] Sin[(3 Pi)/
    19] Sqrt[Pi Cos[(5 Pi)/38] Cos[(9 Pi)/38] Csc[(5 Pi)/
     114] Csc[Pi/19] Csc[(11 Pi)/114] Csc[(2 Pi)/19] Csc[(
     17 Pi)/114] Csc[(23 Pi)/114] Sec[(3 Pi)/38] Sec[(
     11 Pi)/57] Sec[(14 Pi)/57] Sin[Pi/114] Sin[(7 Pi)/
     114] Sin[(13 Pi)/114] Sin[(4 Pi)/19]])/(
  2 2^(13/38) 3^(5/38) 19^(1/6)
    Gamma[5/114] Gamma[11/114] Gamma[2/19] Gamma[17/114] Gamma[23/
    114] Gamma[29/114] Gamma[9/19]), 
 Gamma[43/114] -> (
  2 2^(3/19) 3^(7/19)
    Cos[(5 Pi)/38] Gamma[4/19] Gamma[5/19] Gamma[7/19])/(
  Gamma[5/114] Gamma[8/19]), 
 Gamma[47/114] -> (
  3^(5/19) Cos[Pi/38] Csc[(3 Pi)/19] Gamma[29/114] Gamma[5/
    19] Gamma[9/19] Sec[(5 Pi)/57])/(
  2 2^(6/19) Gamma[3/19] Gamma[8/19]), 
 Gamma[49/114] -> (
  2^(18/19) 3^(4/19)
    Cos[Pi/38] Gamma[4/19] Gamma[5/19] Gamma[9/19] Sec[(3 Pi)/
    38] Sin[(4 Pi)/19])/(Gamma[11/114] Gamma[8/19]), 
 Gamma[53/114] -> (
  3^(2/19) Pi Gamma[2/19] Gamma[23/114] Sec[(2 Pi)/57] Sec[(
    9 Pi)/38])/(2 2^(10/19) Gamma[4/19] Gamma[5/19] Gamma[7/19]), 
 Gamma[55/114] -> (
  2^(14/19) 3^(1/19)
    Cos[(5 Pi)/38] Csc[(2 Pi)/19] Gamma[1/19] Gamma[6/19] Gamma[
    7/19] Sin[Pi/19])/(Gamma[2/19] Gamma[17/114]), 
 Gamma[37/115] -> (
  Csc[(14 Pi)/115] Gamma[9/115] Gamma[32/115] Gamma[11/23] Sec[(
    41 Pi)/230])/(4 5^(5/46) Gamma[14/115] Gamma[9/23]), 
 Gamma[41/115] -> (2^(3/4) 23^(1/10)
      Gamma[2/115] Gamma[4/115] Gamma[1/23] Gamma[7/115] Gamma[9/
      115] Gamma[12/115] Gamma[3/23] Gamma[17/115] Gamma[22/
      115] Gamma[27/115] Gamma[6/23] Gamma[32/115] Gamma[8/23] Gamma[
      11/23] \[Sqrt](Cos[Pi/46] Cos[(7 Pi)/46] Cos[(51 Pi)/
         230] Cos[(11 Pi)/46] Csc[Pi/115] Csc[(3 Pi)/
         115] Csc[(6 Pi)/115] Csc[(8 Pi)/115] Csc[(11 Pi)/
         115] Csc[(13 Pi)/115] Csc[(16 Pi)/115] Csc[(18 Pi)/
         115] Csc[(21 Pi)/115] Csc[(26 Pi)/115] Sec[(33 Pi)/
         230] Sec[(43 Pi)/230] Sec[(53 Pi)/230] Sin[(2 Pi)/
         115] Sin[(4 Pi)/115] Sin[Pi/23] Sin[(7 Pi)/
         115] Sin[(9 Pi)/115] Sin[(12 Pi)/115] Sin[(3 Pi)/
         23] Sin[(17 Pi)/115] Sin[(22 Pi)/115] Sin[(27 Pi)/
         115]))/(5^(7/92) (5 + Sqrt[5])^(1/4)
      Gamma[1/115] Gamma[3/115] Gamma[6/115] Gamma[8/115] Gamma[11/
      115] Gamma[13/115] Gamma[16/115] Gamma[18/115] Gamma[21/
      115] Gamma[26/115] Gamma[31/115] Gamma[36/115] Gamma[2/5]), 
 Gamma[42/115] -> (
  Csc[(19 Pi)/115] Gamma[4/115] Gamma[27/115] Gamma[10/23] Sec[(
    31 Pi)/230])/(4 5^(15/46) Gamma[19/115] Gamma[4/23]), 
 Gamma[44/115] -> (Cos[Pi/46] Cos[(51 Pi)/230] Cos[(11 Pi)/
      46] Csc[Pi/115] Csc[(6 Pi)/115] Csc[(11 Pi)/115] Csc[(
      14 Pi)/115] Csc[(16 Pi)/115] Csc[(19 Pi)/115] Csc[(
      21 Pi)/115] Csc[(24 Pi)/115] Gamma[2/115]^2 Gamma[4/
      115] Gamma[1/23] Gamma[7/115]^2 Gamma[9/115] Gamma[12/
      115]^2 Gamma[17/115]^2 Gamma[22/115]^2 Gamma[5/23] Gamma[27/
      115]^2 Gamma[6/23]^2 Gamma[32/115]^2 Gamma[8/23] Gamma[10/
      23] Gamma[11/23]^2 Sec[(27 Pi)/230] Sec[(37 Pi)/230] Sec[(
      47 Pi)/230] Sec[(57 Pi)/230] Sin[(2 Pi)/115] Sin[Pi/
      23] Sin[(7 Pi)/115] Sin[(12 Pi)/115] Sin[(17 Pi)/
      115] Sin[(22 Pi)/115] Sin[(27 Pi)/115])/(2 5^(15/46) 23^(
     1/10) Sqrt[2 (5 + Sqrt[5])]
      Gamma[1/115] Gamma[3/115] Gamma[6/115] Gamma[8/115] Gamma[2/
      23] Gamma[11/115] Gamma[13/115] Gamma[14/115] Gamma[16/
      115] Gamma[18/115] Gamma[19/115] Gamma[4/23] Gamma[21/
      115] Gamma[1/5] Gamma[24/115] Gamma[28/115] Gamma[29/115] Gamma[
      33/115] Gamma[34/115] Gamma[38/115] Gamma[39/115] Gamma[43/
      115] Gamma[2/5]), 
 Gamma[47/115] -> (
  5^(21/46) Csc[Pi/115] Csc[(24 Pi)/115] Gamma[1/23] Gamma[22/
    115] Gamma[9/23] Sec[(21 Pi)/230] Sin[Pi/23])/(
  4 Gamma[1/115] Gamma[24/115]), 
 Gamma[48/115] -> (Sqrt[2] 5^(2/23)
      Cos[Pi/46] Cos[(51 Pi)/230] Cos[(11 Pi)/46] Csc[Pi/
      115] Csc[(6 Pi)/115] Csc[(11 Pi)/115] Csc[(14 Pi)/
      115] Csc[(16 Pi)/115] Csc[(19 Pi)/115] Csc[(24 Pi)/
      115] Gamma[2/115] Gamma[4/115] Gamma[1/23] Gamma[7/115]^2 Gamma[
      9/115] Gamma[12/115]^2 Gamma[17/115]^2 Gamma[22/115]^2 Gamma[27/
      115]^2 Gamma[6/23]^2 Gamma[32/115]^2 Gamma[8/23] Gamma[10/
      23] Gamma[11/23]^2 Sec[(37 Pi)/230] Sec[(47 Pi)/230] Sec[(
      57 Pi)/230] Sin[(2 Pi)/115] Sin[Pi/23] Sin[(7 Pi)/
      115] Sin[(12 Pi)/115] Sin[(17 Pi)/115] Sin[(22 Pi)/
      115] Sin[(27 Pi)/115])/(23^(1/10) Sqrt[5 + Sqrt[5]]
      Gamma[1/115] Gamma[3/115] Gamma[6/115] Gamma[8/115] Gamma[11/
      115] Gamma[13/115] Gamma[14/115] Gamma[16/115] Gamma[18/
      115] Gamma[19/115] Gamma[4/23] Gamma[1/5] Gamma[24/115] Gamma[
      28/115] Gamma[29/115] Gamma[33/115] Gamma[34/115] Gamma[38/
      115] Gamma[39/115] Gamma[43/115] Gamma[2/5]), 
 Gamma[49/115] -> (
  5^(17/46) Csc[(3 Pi)/115] Csc[(26 Pi)/115] Gamma[3/23] Gamma[
    4/23] Gamma[43/115] Sec[(17 Pi)/230] Sin[(3 Pi)/23])/(
  4 Gamma[3/115] Gamma[26/115]), 
 Gamma[51/115] -> (4 2^(3/4) 5^(19/92) 23^(1/10)
      Gamma[2/115] Gamma[4/115] Gamma[7/115] Gamma[9/115] Gamma[12/
      115] Gamma[3/23] Gamma[17/115] Gamma[22/115] Gamma[5/23] Gamma[
      27/115] Gamma[6/23] Gamma[32/115] Gamma[8/23] Gamma[11/
      23] \[Sqrt](Cos[Pi/46] Cos[(33 Pi)/230] Cos[(7 Pi)/
         46] Cos[(51 Pi)/230] Cos[(11 Pi)/46] Csc[Pi/
         115] Csc[(3 Pi)/115] Csc[(6 Pi)/115] Csc[(8 Pi)/
         115] Csc[(11 Pi)/115] Csc[(13 Pi)/115] Csc[(16 Pi)/
         115] Csc[(21 Pi)/115] Csc[(26 Pi)/115] Sec[(43 Pi)/
         230] Sec[(53 Pi)/230] Sin[(2 Pi)/115] Sin[(4 Pi)/
         115] Sin[Pi/23] Sin[(7 Pi)/115] Sin[(9 Pi)/
         115] Sin[(12 Pi)/115] Sin[(3 Pi)/23] Sin[(17 Pi)/
         115] Sin[(18 Pi)/115] Sin[(22 Pi)/115] Sin[(27 Pi)/
         115]))/((5 + Sqrt[5])^(1/4)
      Gamma[1/115] Gamma[3/115] Gamma[6/115] Gamma[8/115] Gamma[11/
      115] Gamma[13/115] Gamma[16/115] Gamma[21/115] Gamma[26/
      115] Gamma[28/115] Gamma[31/115] Gamma[36/115] Gamma[2/5]), 
 Gamma[52/115] -> (
  5^(11/46) Cos[(11 Pi)/46] Csc[(6 Pi)/115] Gamma[17/115] Gamma[
    6/23] Gamma[8/23] Sec[(11 Pi)/230] Sec[(57 Pi)/230])/(
  4 Gamma[6/115] Gamma[29/115]), 
 Gamma[53/115] -> (
  4 5^(9/46)
    Cos[(37 Pi)/230] Gamma[16/115] Gamma[7/23] Gamma[39/115] Sin[(
    16 Pi)/115])/(Gamma[7/115] Gamma[6/23]), 
 Gamma[54/115] -> (
  5^(7/46) Cos[(7 Pi)/46] Csc[(8 Pi)/115] Gamma[3/23] Gamma[38/
    115] Gamma[8/23] Sec[(7 Pi)/230] Sec[(53 Pi)/230])/(
  4 Gamma[8/115] Gamma[31/115]), 
 Gamma[56/115] -> (
  4 5^(3/46)
    Cos[(43 Pi)/230] Gamma[13/115] Gamma[36/115] Gamma[10/23] Sin[(
    13 Pi)/115])/(Gamma[2/23] Gamma[33/115]), 
 Gamma[57/115] -> (
  5^(1/46) Cos[Pi/46] Csc[(11 Pi)/115] Gamma[12/115] Gamma[7/
    23] Gamma[11/23] Sec[Pi/230] Sec[(47 Pi)/230])/(
  4 Gamma[11/115] Gamma[34/115]), 
 Gamma[27/116] -> (Gamma[1/116] Gamma[5/116] Gamma[9/116] Gamma[3/
      29] Gamma[13/116] Gamma[17/116] Gamma[21/116] Gamma[25/
      116] Gamma[7/29] Gamma[11/
      29] Sqrt[Pi Cos[(7 Pi)/58] Csc[(3 Pi)/116] Csc[(
       7 Pi)/116] Csc[(2 Pi)/29] Csc[(11 Pi)/116] Csc[(
       15 Pi)/116] Csc[(19 Pi)/116] Csc[(23 Pi)/116] Csc[(
       6 Pi)/29] Csc[(27 Pi)/116] Sec[Pi/58] Sec[(9 Pi)/
       58] Sin[Pi/116] Sin[(5 Pi)/116] Sin[(9 Pi)/116] Sin[(
       3 Pi)/29] Sin[(13 Pi)/116] Sin[(17 Pi)/116] Sin[(
       21 Pi)/116] Sin[(25 Pi)/116] Sin[(7 Pi)/29]])/(2^(
     21/58) 29^(1/8)
      Gamma[3/116] Gamma[7/116] Gamma[2/29] Gamma[11/116] Gamma[15/
      116] Gamma[19/116] Gamma[23/116] Gamma[6/29] Gamma[10/29] Gamma[
      14/29]), 
 Gamma[31/116] -> (Csc[Pi/29] Gamma[1/116] Gamma[5/116] Gamma[9/
      116] Gamma[3/29] Gamma[13/116] Gamma[17/116] Gamma[21/
      116] Gamma[25/116] Gamma[7/29] Gamma[11/29] Sec[(27 Pi)/
      116] Sqrt[Pi Cos[(7 Pi)/58] Csc[(3 Pi)/116] Csc[(
       7 Pi)/116] Csc[(11 Pi)/116] Csc[(15 Pi)/116] Csc[(
       19 Pi)/116] Csc[(23 Pi)/116] Csc[(6 Pi)/29] Csc[(
       27 Pi)/116] Sec[Pi/58] Sec[(9 Pi)/58] Sin[Pi/
       116] Sin[(5 Pi)/116] Sin[(2 Pi)/29] Sin[(9 Pi)/
       116] Sin[(3 Pi)/29] Sin[(13 Pi)/116] Sin[(17 Pi)/
       116] Sin[(21 Pi)/116] Sin[(25 Pi)/116] Sin[(7 Pi)/
       29]])/(2^(28/29) 29^(1/8)
      Gamma[3/116] Gamma[1/29] Gamma[7/116] Gamma[11/116] Gamma[15/
      116] Gamma[19/116] Gamma[23/116] Gamma[6/29] Gamma[10/29] Gamma[
      14/29]), 
 Gamma[33/116] -> (
  2 2^(17/58) Gamma[4/29] Gamma[25/116] Sin[(25 Pi)/116])/
  Gamma[2/29], 
 Gamma[35/116] -> (
  2 2^(11/58) Gamma[23/116] Gamma[6/29] Sin[(23 Pi)/116])/
  Gamma[3/29], 
 Gamma[37/116] -> (
  2 2^(5/58) Gamma[21/116] Gamma[8/29] Sin[(21 Pi)/116])/
  Gamma[4/29], 
 Gamma[39/116] -> (
  2^(57/58) Gamma[19/116] Gamma[10/29] Sin[(19 Pi)/116])/
  Gamma[5/29], 
 Gamma[41/116] -> (
  2^(51/58) Gamma[17/116] Gamma[12/29] Sin[(17 Pi)/116])/
  Gamma[6/29], 
 Gamma[43/116] -> (
  2^(45/58) Gamma[15/116] Gamma[14/29] Sin[(15 Pi)/116])/
  Gamma[7/29], 
 Gamma[45/116] -> (
  2^(39/58) Pi Gamma[13/116] Sec[(3 Pi)/58] Sin[(13 Pi)/116])
  /(Gamma[8/29] Gamma[13/29]), 
 Gamma[47/116] -> (Pi Gamma[11/116] Sec[(11 Pi)/116] Sec[(
    11 Pi)/58])/(2 2^(25/58) Gamma[9/29] Gamma[11/29]), 
 Gamma[49/116] -> (
  2^(27/58) Pi Gamma[9/116] Sec[(11 Pi)/58] Sin[(9 Pi)/
    116])/(Gamma[9/29] Gamma[10/29]), 
 Gamma[51/116] -> (
  2^(21/58) Pi Csc[(7 Pi)/29] Gamma[7/116] Sin[(7 Pi)/116])/(
  Gamma[7/29] Gamma[11/29]), 
 Gamma[53/116] -> (
  2^(15/58) Pi Csc[(5 Pi)/29] Gamma[5/116] Sin[(5 Pi)/116])/(
  Gamma[5/29] Gamma[12/29]), 
 Gamma[55/116] -> (
  2^(9/58) Pi Csc[(3 Pi)/29] Gamma[3/116] Sin[(3 Pi)/116])/(
  Gamma[3/29] Gamma[13/29]), 
 Gamma[57/116] -> (
  2^(3/58) Pi Csc[Pi/29] Gamma[1/116] Sin[Pi/116])/(
  Gamma[1/29] Gamma[14/29]), 
 Gamma[43/117] -> (Gamma[1/117] Gamma[2/117] Gamma[5/117] Gamma[10/
      117] Gamma[14/117] Gamma[19/117] Gamma[23/117] Gamma[3/
      13] Gamma[28/117] Gamma[32/117] Gamma[41/117] Sqrt[
     Cos[(35 Pi)/234] Cos[(53 Pi)/234] Csc[(4 Pi)/117] Csc[(
       7 Pi)/117] Csc[(8 Pi)/117] Csc[Pi/13] Csc[Pi/
       9] Csc[(16 Pi)/117] Csc[(17 Pi)/117] Csc[(25 Pi)/
       117] Csc[(2 Pi)/9] Sec[(31 Pi)/234] Sec[(49 Pi)/
       234] Sin[Pi/117] Sin[(2 Pi)/117] Sin[(5 Pi)/117] Sin[(
       10 Pi)/117] Sin[(14 Pi)/117] Sin[(19 Pi)/117] Sin[(
       23 Pi)/117] Sin[(3 Pi)/13] Sin[(28 Pi)/117]])/(3^(
     5/13) 13^(11/36)
      Gamma[4/117] Gamma[7/117] Gamma[8/117] Gamma[1/13] Gamma[1/
      9] Gamma[16/117] Gamma[17/117] Gamma[25/117] Gamma[2/9] Gamma[
      34/117]), 
 Gamma[44/117] -> (2 Cos[(35 Pi)/234] Cos[(53 Pi)/234] Csc[(
      7 Pi)/117] Csc[Pi/13] Csc[(11 Pi)/117] Csc[Pi/
      9] Csc[(16 Pi)/117] Csc[(20 Pi)/117] Csc[(25 Pi)/
      117] Csc[(29 Pi)/117] Gamma[1/117]^2 Gamma[2/117] Gamma[5/
      117] Gamma[10/117]^2 Gamma[14/117]^2 Gamma[19/117]^2 Gamma[23/
      117]^2 Gamma[3/13] Gamma[28/117]^2 Gamma[32/117]^2 Gamma[1/
      3] Gamma[41/117]^2 Gamma[5/13] Sec[(41 Pi)/234] Sec[(
      5 Pi)/26] Sin[Pi/117] Sin[(5 Pi)/117] Sin[(10 Pi)/
      117] Sin[(14 Pi)/117] Sin[(19 Pi)/117] Sin[(23 Pi)/
      117] Sin[(2 Pi)/9] Sin[(3 Pi)/13] Sin[(28 Pi)/
      117])/(3 3^(5/78) 13^(1/3)
      Gamma[4/117] Gamma[7/117] Gamma[8/117] Gamma[1/13]^2 Gamma[11/
      117] Gamma[1/9]^3 Gamma[16/117] Gamma[17/117] Gamma[20/
      117] Gamma[22/117] Gamma[25/117] Gamma[29/117] Gamma[31/
      117] Gamma[35/117] Gamma[4/13] Gamma[38/117] Gamma[6/13]), 
 Gamma[47/117] -> (Cos[(35 Pi)/234] Cos[(53 Pi)/234] Csc[(
      7 Pi)/117] Csc[(8 Pi)/117] Csc[Pi/13] Csc[(11 Pi)/
      117] Csc[Pi/9] Csc[(16 Pi)/117] Csc[(20 Pi)/117] Csc[(
      25 Pi)/117] Csc[(29 Pi)/117] Gamma[1/117]^2 Gamma[2/
      117] Gamma[5/117]^2 Gamma[10/117]^2 Gamma[14/117]^2 Gamma[19/
      117]^2 Gamma[23/117]^2 Gamma[3/13] Gamma[28/117]^2 Gamma[32/
      117]^2 Gamma[1/3] Gamma[41/117]^2 Sec[(23 Pi)/234] Sec[(
      41 Pi)/234] Sec[(5 Pi)/26] Sec[(49 Pi)/234] Sin[Pi/
      117] Sin[(5 Pi)/117] Sin[(10 Pi)/117] Sin[(14 Pi)/
      117] Sin[(19 Pi)/117] Sin[(23 Pi)/117] Sin[(2 Pi)/
      9] Sin[(3 Pi)/13] Sin[(28 Pi)/117])/(12 3^(10/39) 13^(1/3)
      Gamma[4/117] Gamma[7/117] Gamma[8/117]^2 Gamma[1/13]^2 Gamma[11/
      117] Gamma[1/9]^3 Gamma[16/117] Gamma[17/117] Gamma[20/
      117] Gamma[22/117] Gamma[25/117] Gamma[29/117] Gamma[34/
      117] Gamma[35/117] Gamma[4/13] Gamma[38/117]), 
 Gamma[49/117] -> (
  2 13^(1/18)
    Cos[(35 Pi)/234] Cos[(53 Pi)/234] Csc[(7 Pi)/117] Csc[(
    11 Pi)/117] Csc[(20 Pi)/117] Gamma[2/117] Gamma[5/
    117] Gamma[14/117] Gamma[19/117] Gamma[23/117] Gamma[2/9] Gamma[
    28/117] Gamma[32/117]^2 Gamma[1/3] Gamma[41/117]^2 Gamma[5/
    13] Sec[(25 Pi)/234] Sec[(43 Pi)/234] Sin[(5 Pi)/
    117] Sin[(14 Pi)/117] Sin[(23 Pi)/117] Sin[(2 Pi)/9])/(
  3^(11/78) Gamma[4/117] Gamma[7/117] Gamma[11/117] Gamma[1/
    9]^2 Gamma[20/117] Gamma[22/117] Gamma[31/117] Gamma[37/
    117] Gamma[40/117] Gamma[46/117] Gamma[6/13]), 
 Gamma[50/117] -> (
  Csc[(11 Pi)/117] Gamma[2/117] Gamma[28/117] Gamma[41/117] Gamma[
    5/13] Sec[(17 Pi)/234] Sec[(43 Pi)/234])/(
  8 3^(15/26) Gamma[11/117] Gamma[2/13] Gamma[37/117]), 
 Gamma[53/117] -> (
  24 3^(1/26)
    Cos[(41 Pi)/234] Cos[(5 Pi)/26] Gamma[1/13] Gamma[25/
    117] Gamma[4/13] Gamma[38/117] Sin[(25 Pi)/117])/(
  Gamma[1/117] Gamma[14/117] Gamma[40/117]), 
 Gamma[55/117] -> (13^(1/18)
      Cos[(35 Pi)/234] Cos[(53 Pi)/234] Csc[(7 Pi)/
      117] Csc[Pi/13] Csc[(11 Pi)/117] Csc[(16 Pi)/117] Csc[(
      20 Pi)/117] Csc[(29 Pi)/117] Gamma[2/117] Gamma[5/
      117] Gamma[10/117] Gamma[14/117] Gamma[19/117] Gamma[23/
      117]^2 Gamma[2/9] Gamma[3/13] Gamma[28/117] Gamma[32/
      117]^2 Gamma[1/3] Gamma[41/117]^2 Gamma[5/13] Sec[(7 Pi)/
      234] Sec[(25 Pi)/234] Sec[(43 Pi)/234] Sin[(5 Pi)/
      117] Sin[(14 Pi)/117] Sin[(23 Pi)/117] Sin[(2 Pi)/
      9] Sin[(3 Pi)/13])/(4 3^(1/39)
      Gamma[4/117] Gamma[7/117] Gamma[1/13] Gamma[11/117] Gamma[1/
      9]^2 Gamma[16/117] Gamma[20/117] Gamma[22/117] Gamma[29/
      117] Gamma[31/117] Gamma[37/117] Gamma[40/117] Gamma[46/
      117] Gamma[6/13]), 
 Gamma[56/117] -> (3 3^(1/26) 13^(11/36)
      Cos[(5 Pi)/26] Gamma[7/117] Gamma[8/117] Gamma[1/13] Gamma[1/
      9] Gamma[16/117] Gamma[22/117] Gamma[25/117] Gamma[2/9] Gamma[
      34/117] Gamma[35/117] Gamma[4/13] Sec[(5 Pi)/234] Sqrt[
     Cos[(49 Pi)/234] Csc[Pi/117] Csc[(2 Pi)/117] Csc[(
       4 Pi)/117] Csc[(5 Pi)/117] Csc[(10 Pi)/117] Csc[(
       14 Pi)/117] Csc[(17 Pi)/117] Csc[(19 Pi)/117] Csc[(
       23 Pi)/117] Csc[(3 Pi)/13] Csc[(28 Pi)/117] Sec[(
       31 Pi)/234] Sec[(35 Pi)/234] Sec[(53 Pi)/234] Sin[(
       7 Pi)/117] Sin[(8 Pi)/117] Sin[Pi/13] Sin[Pi/
       9] Sin[(16 Pi)/117] Sin[(25 Pi)/117] Sin[(2 Pi)/
       9]])/(8 Gamma[1/117] Gamma[2/117] Gamma[5/117] Gamma[10/
      117] Gamma[14/117] Gamma[19/117] Gamma[23/117] Gamma[28/
      117] Gamma[32/117] Gamma[41/117]), 
 Gamma[58/117] -> (
  8 Cos[(25 Pi)/234] Gamma[7/117] Gamma[20/117] Gamma[46/
    117] Gamma[6/13] Sin[(7 Pi)/117] Sin[(20 Pi)/117])/(
  3^(7/26) Gamma[2/13] Gamma[19/117] Gamma[32/117]), 
 Gamma[44/119] -> (Gamma[1/119] Gamma[4/119] Gamma[5/119] Gamma[8/
      119] Gamma[11/119] Gamma[2/17] Gamma[15/119] Gamma[18/
      119] Gamma[3/17] Gamma[22/119] Gamma[25/119] Gamma[32/
      119] Gamma[39/119] Gamma[6/
      17] \[Sqrt](Cos[(5 Pi)/34] Cos[(41 Pi)/238] Cos[(
         55 Pi)/238] Csc[(2 Pi)/119] Csc[(3 Pi)/119] Csc[(
         6 Pi)/119] Csc[(9 Pi)/119] Csc[(10 Pi)/119] Csc[(
         13 Pi)/119] Csc[(16 Pi)/119] Csc[Pi/7] Csc[(
         20 Pi)/119] Csc[(23 Pi)/119] Csc[(27 Pi)/119] Sec[(
         31 Pi)/238] Sec[(45 Pi)/238] Sec[(59 Pi)/
         238] Sin[Pi/119] Sin[(4 Pi)/119] Sin[(5 Pi)/
         119] Sin[(8 Pi)/119] Sin[(11 Pi)/119] Sin[(2 Pi)/
         17] Sin[(15 Pi)/119] Sin[(18 Pi)/119] Sin[(3 Pi)/
         17] Sin[(22 Pi)/119] Sin[(25 Pi)/119]))/(7^(3/34) 17^(
     1/28) Gamma[2/119] Gamma[3/119] Gamma[6/119] Gamma[9/119] Gamma[
      10/119] Gamma[13/119] Gamma[16/119] Gamma[1/7] Gamma[20/
      119] Gamma[23/119] Gamma[27/119] Gamma[30/119] Gamma[37/119]), 
 Gamma[46/119] -> (
  Csc[(12 Pi)/119] Csc[(29 Pi)/119] Gamma[5/119] Gamma[22/
    119] Gamma[39/119] Gamma[8/17] Sec[(27 Pi)/238])/(
  8 7^(7/34) Gamma[12/119] Gamma[29/119] Gamma[5/17]), 
 Gamma[48/119] -> (Cos[(5 Pi)/34] Cos[(41 Pi)/238] Cos[(
      55 Pi)/238] Csc[(2 Pi)/119] Csc[(6 Pi)/119] Csc[(
      9 Pi)/119] Csc[(12 Pi)/119] Csc[(13 Pi)/119] Csc[(
      16 Pi)/119] Csc[Pi/7] Csc[(19 Pi)/119] Csc[(23 Pi)/
      119] Csc[(26 Pi)/119] Gamma[1/119]^2 Gamma[4/119]^2 Gamma[5/
      119] Gamma[8/119]^2 Gamma[11/119]^2 Gamma[2/17] Gamma[15/
      119]^2 Gamma[18/119]^2 Gamma[3/17] Gamma[22/119]^2 Gamma[25/
      119]^2 Gamma[32/119]^2 Gamma[39/119]^2 Gamma[6/17]^2 Gamma[7/
      17] Gamma[3/7] Sec[(25 Pi)/238] Sec[(39 Pi)/238] Sec[(
      53 Pi)/238] Sec[(59 Pi)/238] Sin[Pi/119] Sin[(4 Pi)/
      119] Sin[(8 Pi)/119] Sin[(11 Pi)/119] Sin[(2 Pi)/
      17] Sin[(15 Pi)/119] Sin[(18 Pi)/119] Sin[(22 Pi)/
      119] Sin[(25 Pi)/119])/(4 7^(7/17) 17^(2/7)
      Gamma[2/119] Gamma[3/119] Gamma[6/119]^2 Gamma[1/17] Gamma[9/
      119] Gamma[10/119] Gamma[12/119] Gamma[13/119]^2 Gamma[16/
      119] Gamma[1/7]^2 Gamma[19/119] Gamma[20/119] Gamma[23/
      119] Gamma[24/119] Gamma[26/119] Gamma[27/119] Gamma[30/
      119] Gamma[31/119] Gamma[33/119] Gamma[2/7] Gamma[40/119] Gamma[
      41/119] Gamma[47/119]), 
 Gamma[50/119] -> (17^(1/14)
      Cos[(41 Pi)/238] Cos[(55 Pi)/238] Csc[(2 Pi)/119] Csc[(
      9 Pi)/119] Csc[(12 Pi)/119] Csc[(16 Pi)/119] Csc[(
      19 Pi)/119] Csc[(26 Pi)/119] Csc[(29 Pi)/119] Gamma[1/
      119] Gamma[4/119] Gamma[5/119] Gamma[8/119] Gamma[11/119] Gamma[
      2/17] Gamma[15/119] Gamma[18/119]^2 Gamma[22/119] Gamma[25/
      119]^2 Gamma[32/119]^2 Gamma[39/119]^2 Gamma[6/17] Gamma[7/
      17] Gamma[3/7] Sec[(19 Pi)/238] Sec[(33 Pi)/238] Sec[(
      47 Pi)/238] Sec[(53 Pi)/238] Sin[(4 Pi)/119] Sin[(
      11 Pi)/119] Sin[(2 Pi)/17] Sin[(18 Pi)/119] Sin[(
      25 Pi)/119])/(16 7^(5/17)
      Gamma[2/119] Gamma[3/119] Gamma[1/17] Gamma[9/119] Gamma[10/
      119] Gamma[12/119] Gamma[16/119] Gamma[1/7] Gamma[19/119] Gamma[
      24/119] Gamma[26/119] Gamma[29/119] Gamma[31/119] Gamma[33/
      119] Gamma[36/119] Gamma[38/119] Gamma[43/119] Gamma[45/119]), 
 Gamma[52/119] -> (7^(5/34) 17^(1/14)
      Cos[(41 Pi)/238] Cos[(55 Pi)/238] Csc[(2 Pi)/119] Csc[(
      9 Pi)/119] Csc[(12 Pi)/119] Csc[(19 Pi)/119] Csc[(
      26 Pi)/119] Csc[(29 Pi)/119] Gamma[4/119] Gamma[5/
      119] Gamma[8/119] Gamma[11/119] Gamma[2/17] Gamma[15/119] Gamma[
      18/119] Gamma[22/119] Gamma[25/119]^2 Gamma[32/119]^2 Gamma[39/
      119]^2 Gamma[6/17] Gamma[7/17] Gamma[3/7] Sec[(33 Pi)/
      238] Sec[(47 Pi)/238] Sin[(4 Pi)/119] Sin[(11 Pi)/
      119] Sin[(2 Pi)/17] Sin[(18 Pi)/119] Sin[(25 Pi)/
      119])/(2 Gamma[2/119] Gamma[3/119] Gamma[9/119] Gamma[10/
      119] Gamma[12/119] Gamma[1/7] Gamma[19/119] Gamma[24/119] Gamma[
      26/119] Gamma[29/119] Gamma[31/119] Gamma[5/17] Gamma[36/
      119] Gamma[38/119] Gamma[43/119] Gamma[45/119]), 
 Gamma[53/119] -> (
  7^(13/34) Csc[(2 Pi)/119] Csc[(19 Pi)/119] Gamma[2/17] Gamma[
    15/119] Gamma[32/119] Gamma[7/17] Sec[(13 Pi)/238] Sec[(
    47 Pi)/238] Sin[(2 Pi)/17])/(
  8 Gamma[2/119] Gamma[19/119] Gamma[36/119]), 
 Gamma[54/119] -> (Cos[(5 Pi)/34] Cos[(41 Pi)/238] Cos[(
      55 Pi)/238] Csc[(2 Pi)/119] Csc[(3 Pi)/119] Csc[(
      6 Pi)/119] Csc[(9 Pi)/119] Csc[(12 Pi)/119] Csc[(
      13 Pi)/119] Csc[(16 Pi)/119] Csc[Pi/7] Csc[(19 Pi)/
      119] Csc[(20 Pi)/119] Csc[(23 Pi)/119] Csc[(26 Pi)/
      119] Gamma[1/119]^2 Gamma[4/119]^2 Gamma[5/119] Gamma[8/
      119]^2 Gamma[11/119]^2 Gamma[2/17]^2 Gamma[15/119]^2 Gamma[18/
      119]^2 Gamma[3/17]^2 Gamma[22/119]^2 Gamma[25/119]^2 Gamma[32/
      119]^2 Gamma[39/119]^2 Gamma[6/17]^2 Gamma[7/17] Gamma[3/
      7] Sec[(11 Pi)/238] Sec[(25 Pi)/238] Sec[(39 Pi)/
      238] Sec[(45 Pi)/238] Sec[(53 Pi)/238] Sec[(59 Pi)/
      238] Sin[Pi/119] Sin[(4 Pi)/119] Sin[(8 Pi)/119] Sin[(
      11 Pi)/119] Sin[(2 Pi)/17] Sin[(15 Pi)/119] Sin[(
      18 Pi)/119] Sin[(3 Pi)/17] Sin[(22 Pi)/119] Sin[(
      25 Pi)/119])/(32 7^(3/34) 17^(2/7)
      Gamma[2/119] Gamma[3/119]^2 Gamma[6/119]^2 Gamma[1/17] Gamma[9/
      119] Gamma[10/119] Gamma[12/119] Gamma[13/119]^2 Gamma[16/
      119] Gamma[1/7]^2 Gamma[19/119] Gamma[20/119]^2 Gamma[23/
      119] Gamma[24/119] Gamma[26/119] Gamma[27/119] Gamma[30/
      119] Gamma[33/119] Gamma[2/7] Gamma[37/119] Gamma[40/119] Gamma[
      41/119] Gamma[47/119]), 
 Gamma[55/119] -> (
  8 7^(9/34)
    Cos[(25 Pi)/238] Cos[(59 Pi)/238] Gamma[13/119] Gamma[4/
    17] Gamma[30/119] Gamma[47/119] Sin[(13 Pi)/119])/(
  Gamma[4/119] Gamma[3/17] Gamma[38/119]), 
 Gamma[57/119] -> (
  7^(5/34) Cos[(5 Pi)/34] Csc[(6 Pi)/119] Csc[(23 Pi)/
    119] Gamma[11/119] Gamma[4/17] Gamma[6/17] Gamma[45/119] Sec[(
    5 Pi)/238] Sec[(39 Pi)/238])/(
  8 Gamma[6/119] Gamma[23/119] Gamma[40/119]), 
 Gamma[58/119] -> (8 Gamma[1/119] Gamma[4/119] Gamma[5/119] Gamma[8/
      119] Gamma[11/119] Gamma[2/17] Gamma[15/119] Gamma[18/
      119] Gamma[3/17] Gamma[22/119] Gamma[25/119] Gamma[32/
      119] Gamma[39/119] Gamma[6/17] Gamma[7/
      17] \[Sqrt](Cos[(31 Pi)/238] Cos[(5 Pi)/34] Cos[(
         41 Pi)/238] Cos[(55 Pi)/238] Csc[(2 Pi)/119] Csc[(
         3 Pi)/119] Csc[(6 Pi)/119] Csc[(9 Pi)/119] Csc[(
         13 Pi)/119] Csc[(16 Pi)/119] Csc[Pi/7] Csc[(
         20 Pi)/119] Csc[(23 Pi)/119] Sec[(45 Pi)/238] Sec[(
         59 Pi)/238] Sin[Pi/119] Sin[(4 Pi)/119] Sin[(
         5 Pi)/119] Sin[(8 Pi)/119] Sin[(10 Pi)/119] Sin[(
         11 Pi)/119] Sin[(2 Pi)/17] Sin[(15 Pi)/119] Sin[(
         18 Pi)/119] Sin[(3 Pi)/17] Sin[(22 Pi)/119] Sin[(
         25 Pi)/119] Sin[(27 Pi)/119]))/(17^(1/28)
      Gamma[2/119] Gamma[3/119] Gamma[6/119] Gamma[1/17] Gamma[9/
      119] Gamma[13/119] Gamma[16/119] Gamma[1/7] Gamma[20/119] Gamma[
      23/119] Gamma[24/119] Gamma[30/119] Gamma[37/119] Gamma[41/
      119]), Gamma[59/119] -> (
  8 7^(1/34)
    Cos[(33 Pi)/238] Gamma[9/119] Gamma[26/119] Gamma[43/
    119] Gamma[8/17] Sin[(9 Pi)/119] Sin[(26 Pi)/119])/(
  Gamma[8/119] Gamma[25/119] Gamma[6/17]), 
 Gamma[13/120] -> -((
   2 2^(13/30) 3^(7/40) 5^(7/8)
     Csc[Pi/40] Csc[(7 Pi)/120] Csc[(2 Pi)/15] Csc[(3 Pi)/
     20] Gamma[7/60] Gamma[1/8]^2 Gamma[7/40]^2 Gamma[1/5] Sin[Pi/
     60] Sin[Pi/8]^2 Sin[(7 Pi)/
     40])/((-1 + Sqrt[3]) (-5 + Sqrt[5]) Gamma[1/40] Gamma[7/
     120] Gamma[3/40] Gamma[1/4] Gamma[2/5])), 
 Gamma[17/120] -> (
  2 2^(43/60)
    Csc[Pi/60] Csc[Pi/8] Csc[(7 Pi)/40] Gamma[1/120] Gamma[7/
    120] Gamma[3/40]^2 Gamma[11/120] Gamma[1/4] Gamma[2/5] Sin[(
    7 Pi)/120] Sin[(3 Pi)/40] Sin[(11 Pi)/
    120] Sqrt[(-1 + Sqrt[3]) Sin[Pi/20] Sin[Pi/15] Sin[(
     2 Pi)/15] Sin[(3 Pi)/20]])/(
  3^(1/4) 5^(3/8) Gamma[1/60] Gamma[1/8]^2 Gamma[7/40]^2 Gamma[1/5]), 
 Gamma[19/120] -> (
  2 2^(1/30) 3^(1/40)
    Csc[Pi/120] Csc[Pi/20] Gamma[1/60] Gamma[1/40] Gamma[7/
    40] Sin[Pi/60] Sin[Pi/40] Sin[(7 Pi)/40])/(
  Gamma[1/120] Gamma[1/20]), 
 Gamma[23/120] -> (
  Csc[Pi/8] Sqrt[(Pi Csc[Pi/15] Csc[(2 Pi)/15])/(-1 + 
    Sqrt[3])]
    Csc[(3 Pi)/20] Csc[(7 Pi)/40] Gamma[1/120] Gamma[1/
    40] Gamma[7/120] Gamma[3/40] Gamma[11/120] Gamma[1/4] Sin[Pi/
    120] Sin[(3 Pi)/40])/(
  2^(14/15) 3^(13/40) 5^(1/4) (5 - Sqrt[5])^(3/4)
    Gamma[1/60] Gamma[1/8]^2 Gamma[7/40]^2 Gamma[1/5]), 
 Gamma[29/120] -> (
  5^(3/8) (Sqrt[3] - 2 Cos[Pi/60]) Csc[(7 Pi)/40] Gamma[1/
    40] Gamma[3/40]^2 Gamma[11/120] Gamma[1/4] Gamma[2/5])/(
  Sqrt[2] 3^(
   9/40) (-5 + Sqrt[5]) Gamma[1/20] Gamma[1/8]^2 Gamma[7/40] Gamma[1/
    5]), Gamma[31/120] -> (
  3^(9/40) 5^(5/24)
    Csc[Pi/20] Csc[Pi/8]^2 Gamma[1/40] Gamma[3/40]^2 Gamma[11/
    120] Gamma[1/4] Gamma[1/3] Gamma[2/5] Sin[Pi/40] Sin[(3 Pi)/
    40])/(2 2^(11/30) (5 - Sqrt[5])^(1/4)
    Gamma[1/60] Gamma[1/20] Gamma[1/8]^2 Gamma[7/
    40] Sqrt[Pi Sin[Pi/15] Sin[(2 Pi)/15]]), 
 Gamma[37/120] -> ((-1 + Sqrt[3]) (5/8 - Sqrt[5]/8)^(3/2)
    Csc[Pi/60] Csc[Pi/20] Csc[Pi/15] Csc[Pi/8]^3 Gamma[1/
    120] Gamma[1/40] Gamma[7/120] Gamma[3/40] Gamma[11/120] Gamma[1/
    4] Gamma[1/3] Gamma[2/5] Sec[Pi/8] Sec[(7 Pi)/30] Sin[Pi/
    40]^2 Sin[(3 Pi)/20] Sqrt[
   Cos[Pi/120] Cot[(29 Pi)/120] Csc[Pi/24] Csc[(23 Pi)/
     120] Sec[(23 Pi)/120] Sin[Pi/120] Sin[(5 Pi)/24] Tan[(
     7 Pi)/120]])/(
  20 3^(7/40) 5^(1/6)
    Gamma[1/60] Gamma[7/60] Gamma[1/8]^2 Gamma[7/40]^2 Gamma[1/5]), 
 Gamma[41/120] -> (
  3^(19/40) 5^(3/8)
    Csc[(7 Pi)/120] Csc[Pi/15] Csc[(11 Pi)/120] Csc[(
    2 Pi)/15] Csc[(17 Pi)/120] Gamma[1/40] Gamma[7/40] Gamma[1/
    5] Sec[Pi/8] Sec[(19 Pi)/120] Sin[Pi/60] Sin[Pi/
    40] Sin[(7 Pi)/40] Sqrt[(
   Csc[Pi/120] Csc[Pi/24] Csc[(3 Pi)/20] Csc[(19 Pi)/
     120] Csc[(23 Pi)/120] Csc[(29 Pi)/120] Sec[(7 Pi)/
     120] Sec[(11 Pi)/120] Sec[(13 Pi)/120] Sec[(17 Pi)/
     120] Sin[(5 Pi)/24])/(-1 + Sqrt[3])])/(
  512 (5 - Sqrt[5])^(1/4) Gamma[1/120] Gamma[1/20] Sin[Pi/20]^(
   3/2)), Gamma[43/120] -> ((5 - Sqrt[5])^(5/4) (3/(5 + Sqrt[5]))^(
   1/4) Csc[Pi/60]^2 Csc[Pi/24] Csc[Pi/8]^2 Csc[(19 Pi)/
    120] Csc[(7 Pi)/40] Gamma[1/120] Gamma[7/120] Gamma[3/
    40]^2 Gamma[11/120] Gamma[1/4] Gamma[1/3] Gamma[2/5] Sec[Pi/
    8] Sec[(17 Pi)/120] Sqrt[
   1/2 Cos[Pi/120] Cot[(23 Pi)/120] Cot[(29 Pi)/120] Sec[(
     7 Pi)/120] Sin[Pi/120]]
    Sin[Pi/40] ((-1 + Sqrt[3]) Sin[(7 Pi)/120])^(3/2)
    Sin[(11 Pi)/120] Sin[(2 Pi)/15] Sin[(3 Pi)/20]^2 Sin[(
    5 Pi)/24])/(
  4 5^(11/12)
    Gamma[1/60] Gamma[7/60] Gamma[1/8]^2 Gamma[7/40]^2 Gamma[1/5]), 
 Gamma[47/120] -> (
  3^(13/40) (5 + Sqrt[5])^(3/4)
    Csc[Pi/30] Csc[Pi/24] Csc[(3 Pi)/40] Csc[(7 Pi)/
    60] Csc[(2 Pi)/15] Csc[(19 Pi)/120] Csc[(23 Pi)/
    120] Csc[(7 Pi)/30] Csc[(29 Pi)/120] Gamma[1/8]^2 Gamma[7/
    40]^2 Gamma[1/5] Sin[Pi/15]^2 Sin[(13 Pi)/120] Sin[Pi/
    8]^2 Sin[(7 Pi)/40] Sin[(5 Pi)/24] Sqrt[
   Csc[Pi/20] Sin[Pi/30] Sin[(3 Pi)/20] Sin[(7 Pi)/30]])/(
  2 2^(4/5) Gamma[1/40] Gamma[7/120] Gamma[3/40] Gamma[1/4]), 
 Gamma[49/120] -> -((
   5^(11/24)
     Cos[(7 Pi)/30] Csc[(7 Pi)/120] Csc[Pi/15] Csc[(2 Pi)/
     15] Csc[(17 Pi)/120] Gamma[11/120] Gamma[1/3] Sec[Pi/
     8] Sin[Pi/120] Sqrt[(
    3 (5 + Sqrt[5]) Cos[Pi/120] Cos[(23 Pi)/120] Cos[(29 Pi)/
      120] Csc[Pi/24] Csc[Pi/20] Csc[(3 Pi)/20] Csc[(
      19 Pi)/120] Sec[(11 Pi)/120] Sec[(13 Pi)/120] Sec[(
      17 Pi)/120] Sin[(7 Pi)/120] Sin[Pi/15] Sin[(2 Pi)/
      15] Sin[(5 Pi)/24])/(-1 + Sqrt[3])])/(
   2 2^(49/60) (-5 + Sqrt[5]) Gamma[1/60])), 
 Gamma[53/120] -> ((-1 + Sqrt[3])^(3/2) (5 - Sqrt[5])^(9/4)
    Csc[Pi/120] Csc[Pi/60] Csc[Pi/20] Csc[(3 Pi)/40] Csc[(
    7 Pi)/60] Csc[Pi/8] Csc[(23 Pi)/120] Csc[(29 Pi)/
    120] Gamma[7/120] Sin[Pi/40]^2 Sin[(7 Pi)/120]^2 Sin[(
    2 Pi)/15] Sin[(3 Pi)/20]^2 Sin[(7 Pi)/
    40] Sqrt[Pi Csc[Pi/24] Sin[Pi/30] Sin[(5 Pi)/24] Sin[(
     7 Pi)/30]])/(10 2^(23/60) (5 + Sqrt[5])^(1/4) Gamma[7/60]), 
 Gamma[59/120] -> (
  Csc[Pi/60] Csc[Pi/20] Csc[Pi/15]^2 Csc[(11 Pi)/
    120] Csc[Pi/8]^2 Csc[(2 Pi)/
    15] Sqrt[(5 - Sqrt[5]) Pi Csc[(7 Pi)/30]]
    Csc[(29 Pi)/120] Gamma[1/120] Sin[Pi/120] Sin[Pi/
    40] Sin[Pi/30]^(3/2) Sin[(7 Pi)/40] Sin[(7 Pi)/30])/(
  8 2^(59/60) 5^(1/4) Gamma[1/60])}];

GammaExpand[expr_] := expr /. gammaRules;

End[];

EndPackage[];
