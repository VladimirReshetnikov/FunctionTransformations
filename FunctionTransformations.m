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

SetAttributes[{polyLogRules, PolyLogExpand}, ReadProtected];

End[];

EndPackage[];
