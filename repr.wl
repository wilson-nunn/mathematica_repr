(* ::Package:: *)

(* PolynomialVars[d,var] produces a list of d enumerated symbols where var is the symbol.
   var is an optional argument and if left out will default to var=x *)
ClearAll[PolynomialVars];
PolynomialVars[d_,var_:"x"]:=Table[ToExpression[ToString[var]<>ToString[k]],{k,1,d}]

(* Monomials[m,d,var] produces a list of all monomials from degree 0 up to degree m in
   d variables where var is the symbol used. d and var are optional arguments and if
   left out will default to d=2 and var=x *)
ClearAll[Monomials];
Monomials[m_,d_:2,var_:"x"]:=Flatten[Prepend[Table[Table[If[Head[k]===Times,k/k[[1]],k],
   {k,MonomialList[(Total[PolynomialVars[d,var]])^k1,PolynomialVars[d,var]]}],{k1,1,m}],1]]
   
(* Chebyshevs[m,d] produces a list of all Chebyshev polynomials from degree 0 up to degree m in
   d variables. d is an optional argument and if left out will default to d=2. 
   Chebyshevs[m,lims,d] produces the same except the Chebyshev polynomials are transalted and
   scaled to be within the range of lims. *)
ClearAll[Chebyshevs];
Chebyshevs[m_,d_:2]:=Module[{vars,tuples,result},
vars=PolynomialVars[d];
tuples=Table[With[{iter=Apply[{#2,#1,Length[vars]}&,Partition[Prepend[Array[Unique[]&,k],1],2,1],{1}]},
	(Part[vars,#1]&)/@Flatten[Table@@{iter[[All,1]],Sequence@@iter},k-1]],{k,1,m}];
Prepend[Flatten[Table[Expand[(Apply[Times,Apply[ChebyshevT,#,{1}]]&/@Table[{Count[i,j],j},
    {i,tuples[[k]]},{j,vars}])],{k,1,Length[tuples]}]],1]]
Chebyshevs[m_,{A_,B_},d_:2]:=Chebyshevs[m,d]/.(x1->(2/(B-A) x1-(-A-B)/(A-B)))


(* NewIntegrate[integrang,lower,upper,nvars] computes the integral of integrant between lower
   and upper with respect to the number variables nvars *)
ClearAll[NewIntegrate];
NewIntegrate[integrand_,lower_,upper_,nvars_]:=Integrate[integrand,
    Evaluate[Sequence @@ Table[{var,lower,upper},{var,PolynomialVars[nvars]}]]]


(* Compute the basis functions for use in REPR when fiting a degree m polynomial to data of
    dimension d where the regions are lims1 and lims2. This function is used to pick the
    default polynomial basis, Chebyshev or standard monomials *)
ClearAll[LinearMappingBasisFunctions];
LinearMappingBasisFunctions[m_,d_,lims1_,lims2_]:=LinearMappingBasisFunctionsChebyshev[m,d,lims1,lims2]
(*LinearMappingBasisFunctions[m_,d_,lims1_,lims2_]:=LinearMappingBasisFunctionsMonomial[m,d,lims1,lims2]*)

(* Compute the basis functions using Chebyshev polynomials *)
ClearAll[LinearMappingBasisFunctionsChebyshev];
LinearMappingBasisFunctionsChebyshev[m_,d_,lims1_,lims2_]:=LinearMappingBasisFunctionsChebyshev[m,d,lims1,lims2]=Block[{\[Eta],matrix1,eigenSystem},
    \[Eta]=Chebyshevs[m,lims2,d];
    matrix1=Inverse[ParallelTable[NewIntegrate[(i*j),lims1[[1]],lims1[[2]],d],{i,\[Eta]},{j,\[Eta]}]] . ParallelTable[NewIntegrate[(i*j),lims2[[1]],lims2[[2]],d],{i,\[Eta]},{j,\[Eta]}];
    eigenSystem=Eigensystem@(N[matrix1]);
    eigenSystem[[2]]=eigenSystem[[2]] . \[Eta];
    eigenSystem]

(* Compute the basis functions using Chebyshev polynomials *)
ClearAll[LinearMappingBasisFunctionsMonomial];
LinearMappingBasisFunctionsMonomial[m_,d_,lims1_,lims2_]:=LinearMappingBasisFunctionsMonomial[m,d,lims1,lims2]=Block[{\[Eta],matrix1,eigenSystem},
    \[Eta]=Monomials[m,d];
    matrix1=Inverse[ParallelTable[NewIntegrate[(i*j),lims1[[1]],lims1[[2]],d],{i,\[Eta]},{j,\[Eta]}]] . ParallelTable[NewIntegrate[(i*j),lims2[[1]],lims2[[2]],d],{i,\[Eta]},{j,\[Eta]}];
    eigenSystem=Eigensystem@N[(matrix1)];
    eigenSystem[[2]]=eigenSystem[[2]] . \[Eta];
    eigenSystem]


(* Extract the coefficients of a polynomial as a list, works with polynomials in any
    dimension and any degree *)
ClearAll[coefF]
coefF[poly_]:=Block[{vars},
	vars =PolynomialVars[d];
	First@@@CoefficientRules[Monomials[m,d],vars]/.CoefficientRules[Expand[poly],vars]/.{_,_}:>0]

(* Select which basis functions to use in REPR *)
ClearAll[EigenFunctionSelection];
EigenFunctionSelection[eFuncs_,eVals_,xVals_]:=EigenFunctionSelection[eFuncs,eVals,xVals]=Block[{eFuncSelections,idx},
	eFuncSelections=
	(Table[eFuncs[[i,-#[[i]];;]],{i,Length[eFuncs]}]&/@Cases[Table[Length/@(Cases[#,x_/;x<=k]&/@eVals),{k,Union@@eVals}],
		y_/;And[Not[MemberQ[y,0]],AllTrue[(Length/@xVals)-y,Not[Negative[#]]&]]]);
	idx=Cases[Table[{i,Total[Length/@eFuncSelections[[i]]],MatrixRank[coefF/@Flatten[eFuncSelections[[i]]]]},
		{i,1,Length[eFuncSelections]}],x_/;x[[2]]<=x[[3]]][[All,1]];
	eFuncSelections[[idx]]]

(* Select which basis functions to use in REPR and make in a displayable format *)
ClearAll[EigenFunctionSelectionDisplay];
EigenFunctionSelectionDisplay[eFuncs_,eVals_,xVals_]:=EigenFunctionSelectionDisplay[eFuncs,eVals,xVals]=Block[{eFuncSelections,idx,idx2},
	eFuncSelections=
	(Table[eFuncs[[i,-#[[i]];;]],{i,Length[eFuncs]}]&/@Cases[Table[Length/@(Cases[#,x_/;x<=k]&/@eVals),{k,Union@@eVals}],
		y_/;And[Not[MemberQ[y,0]],AllTrue[(Length/@xVals)-y,Not[Negative[#]]&]]]);
	idx=Cases[Table[{i,Total[Length/@eFuncSelections[[i]]],MatrixRank[coefF/@Flatten[eFuncSelections[[i]]]]},
		{i,1,Length[eFuncSelections]}],x_/;x[[2]]<=x[[3]]][[All,1]];
	idx2=Cases[Table[Length/@(Cases[#,x_/;x<=k]&/@eVals),{k,Union@@eVals}],y_/;And[Not[MemberQ[y,0]],AllTrue[(Length/@xVals)-y,Not[Negative[#]]&]]];
	idx2[[idx]]]


(* Fit initial model in the REPR methodology *)
ClearAll[LinearModelsFirst];
LinearModelsFirst[d_,xVals_,yVals_,eFuncs_,eVals_]:=Block[{vars,eFuncSelections,partModels1, partModels2},
	vars=PolynomialVars[d];
	eFuncSelections=EigenFunctionSelection[eFuncs,eVals,xVals];
	partModels1=Table[LinearModelFit[MapThread[Append,{xVals[[j]],yVals[[j]]}],eFunc[[j]],vars,
		IncludeConstantBasis->False]@@PolynomialVars[d,"t"],{j,1,Length[xVals]},{eFunc,eFuncSelections}];
	partModels2=Apply[Plus,#]&/@Transpose[PadRight[#,Max[Length/@partModels1],#[[-1]]]&/@partModels1];
	Function[Evaluate[PolynomialVars[d,"t"]],Evaluate[#]]&/@partModels2]
	
(* Fit iterations of the REPR model *)
ClearAll[LinearModelsIteration];
LinearModelsIteration[d_,initialModels_,xVals_,yVals_,eFuncs_,eVals_]:=Block[{vars,fitted,eFuncSelections,corrections1, corrections2},
	vars=PolynomialVars[d];
	fitted=Table[yVals[[i]]-model@@@xVals[[i]],{i,1,Length[xVals]},{model,initialModels}];
	eFuncSelections=EigenFunctionSelection[eFuncs,eVals,xVals];
	corrections1=Table[LinearModelFit[MapThread[Append,{xVals[[j]],fitted[[j,i]]}],eFuncSelections[[i,j]],vars,
		IncludeConstantBasis->False]@@PolynomialVars[d,"t"],{j,1,Length[xVals]},{i,1,Length[eFuncSelections]}];
	corrections2=Apply[Plus,#]&/@Transpose[PadRight[#,Max[Length/@corrections1],#[[-1]]]&/@corrections1];
	Function[Evaluate[PolynomialVars[d,"t"]],Evaluate[initialModels[[#]]@@PolynomialVars[d,"t"]+corrections2[[#]]]]&/@Range[1,Length[initialModels]]]
