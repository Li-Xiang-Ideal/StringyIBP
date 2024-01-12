(* ::Package:: *)

(* ::Subsection:: *)
(*Initialize*)


SetDirectory[NotebookDirectory[]];
<<StringyIBP.m


(* ::Subsection:: *)
(*Demo*)


Init[Null,1(* initialized/default value *)]
Init[Missing,1]
Init[List[](* use default value if input=Null|Missing|{} *),1]
Init[a+b,1]


ExtractVariableList[f[1]+g[2]+Sqrt[f[3,6]]+h[4]^g[4]+g[5]/3,f](* extract _f *)
ExtractVariableList[f[1]+g[2]+Sqrt[f[3,6]]+h[4]^g[4]+g[5]/3,{f,g}](* extract _f|_g *)
ExtractVariableList[{-1,-2,a,b,3,5,-6},Integer](* sort by default order *)
ExtractVariableList[{-1,-2,a,b,3,5,-6},Integer,Abs(* sort by Abs *)]
ExtractVariableList[{-1,-2,a,b,3,5,-6},Integer,0&(* sort by 0& i.e. do not sort *)]


ExtractVariableFold[(3+Subscript[X, 1,3])int[1+Subscript[X, 1,3],2+Subscript[X, 1,4],Subscript[X, 2,4],Subscript[X, 2,5],Subscript[X, 3,5]],_int,_Integer+Subscript[X, __]](* extract _int, then extract _+Subscript[X, __] from all the int[___]. 3+Subscript[X, 1,3] is not extracted *)
ExtractVariableFold[(3+Subscript[X, 1,3])int[1+Subscript[X, 1,3],2+Subscript[X, 1,4],Subscript[X, 2,4],Subscript[X, 2,5],Subscript[X, 3,5]],_int,_Integer+Subscript[X, __],{_Integer,{2}}(* extract _Integer from level 2 *)]


ExtractVarSubscript[Subscript[a, 1]+Subscript[b, 2]+Sqrt[Subscript[b, 3,7]]+a[4]^Subscript[a, 4,5,6]+b[5]/3,a](* extract Subscript[a, __] *)
ExtractVarSubscript[Subscript[a, 1]+Subscript[b, 2]+Sqrt[Subscript[b, 3,7]]+a[4]^Subscript[a, 4,5,6]+b[5]/3,{a,b}](* extract Subscript[a, __]|Subscript[b, __] *)


Xvars[5]
Xvars[5,"X"->u(* replace X by u *)]


Xcvars[5](* default triangulation: Subscript[X, 1,i] *)
Xcvars[5,"X"->x(* replace X by x *),"c"->cc(* replace c by cc *)]
Xcvars[5,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}(* triangulation *)]
(* Here we delete Subscript[c, i-1,j-1] instead of Subscript[c, i,j]!!! *)


Xcal[5]
Xcal[5,"X"->x(* replace X by x *)]
ctoX[5]
ctoX[5,"X"->x,"c"->cc]
Xtoc[5](* default triangulation: Subscript[X, i,n] *)
Xtoc[5,"X"->x,"c"->cc]
Xtoc[5,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}(* triangulation *)]
Xtoc[5,"X"->x,"c"->cc,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}]


int[Subscript[X, 1,3],Subscript[X, 1,4],Subscript[c, 1,3],Subscript[c, 1,4],1+Subscript[c, 2,4]]+int[Subscript[X, 1,3],Subscript[X, 1,4],Subscript[c, 1,3],1+Subscript[c, 1,4],Subscript[c, 2,4]]//int$XctoX
%//int$XtoXc


int$XctoX[int[Subscript[X, 2,5],Subscript[X, 3,5],Subscript[c, 1,3],Subscript[c, 2,5],1+Subscript[c, 3,5]],"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}(* triangulation *)]
int$XtoXc[%,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}(* triangulation *)]


RuleDelayed@@{Subscript[X, 1,3]/.XctoPattern,1+Subscript[X, 1,3]/.XctoVarName}
RuleDelayed@@{Subscript[X, 1,3]+Subscript[X, 1,4]/.XctoPatternIf[Subscript[X, 1,4],Positive],1+Subscript[X, 1,3]+Subscript[X, 1,4]/.XctoVarName}


int[1+Subscript[X, 2,5],1+Subscript[X, 3,5],Subscript[X, 1,3],Subscript[X, 1,4],Subscript[X, 2,4]]/.XctoStdOrd
int[Subscript[X, 1,3],1+Subscript[X, 2,5],1+Subscript[X, 3,5],Subscript[X, 1,4],Subscript[X, 2,4]]/.XctoStdOrd


Xc$cyclicPerm[int[Subscript[X, 1,3],Subscript[X, 1,4],Subscript[X, 2,4],Subscript[X, 2,5],1+Subscript[X, 3,5]],5(* n=5 *),0]
Xc$cyclicPerm[int[Subscript[X, 1,3],Subscript[X, 1,4],Subscript[X, 2,4],Subscript[X, 2,5],1+Subscript[X, 3,5]],5,1]
Xc$cyclicPerm[int[Subscript[X, 1,3],Subscript[X, 1,4],Subscript[X, 2,4],Subscript[X, 2,5],1+Subscript[X, 3,5]],5,2]


utoyRules[5]
utoyRules[5,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}]


StringyIntegrand$X[5]
StringyIntegrand$Xc[5]
StringyIntegrand$Xc[5,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}]
StringyIntegrand$Xc[6,"Triangulation"->{Subscript[X, 1,3],Subscript[X, 3,5],Subscript[X, 1,5]}]


StringyPolynomial[5,1,3,"Triangulation"->{}(* default triangulation Subscript[X, 1,i] *)](* Subscript[p, 1,3] *)
StringyPolynomial[5,1,3,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}]


TrivialIdentity$X[5,1,3](* trivial identity obtained from expansion of Subscript[p, 1,3][y] *)
TrivialIdentity$Xc[5,1,3]
TrivialIdentity$X[5,1,3,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]},"F Polynomial"->StringyPolynomial(* input F polynomials *)]


IBP$Identity$X[5,1](* IBP identity obtained from derivative of Subscript[y, 1] *)
IBP$Identity$Xc[5,1]
IBP$Identity$X[5,1,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]},"F Polynomial"->StringyPolynomial(* input F polynomials *)]


CheckStringyIdentity[TrivialIdentity$X[5,1,3]]
CheckStringyIdentity[TrivialIdentity$Xc[5,1,3,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}],"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}(* check under non-default triangulation *)]
CheckStringyIdentity[IBP$Identity$Xc[5,1]]


StringyIdentity$X[5](* identities directly obtained from expansion of p[y] or derivative of Subscript[y, i] *)
StringyIdentity$Xc[5, "Triangulation" -> {Subscript[X, 2, 5], Subscript[X, 3, 5]}]


StringyIdentity$X$shift[5](* various shift of original identities *)
StringyIdentity$X$shift[5,"Triangulation"->{Subscript[X, 2,5],Subscript[X, 3,5]}(* use non-default triangulation *),"cutoff"->{1(* default: shift\[LessEqual]1 *),True(* default: enable single shift=1+1 *)}]


StringyIdentity$X$All[5](* cyclic *)


intXs$List[5]
intXs$List[5,"cutoff"->{2(* shift\[LessEqual]2 *),False(* disable single shift=2+1 *)}]


StringyReductionDataFF$X[5]


(* ::Subsection:: *)
(*Calculation*)


(* ::Subsubsection:: *)
(*5pt*)


StringyReduction$X[5];
%//MatrixForm


StringyAscendRules$X[5]


StringyDescendRules$X[5]


Collect[int[-1+Subscript[X, 1,3],Subscript[X, 1,4],1+Subscript[X, 2,4],1+Subscript[X, 2,5],Subscript[X, 3,5]]//.StringyAscendRules$X[5]//.StringyDescendRules$X[5],intXs$List[5]]//Simplify(* reduce to master integral *)


(* ::Subsubsection:: *)
(*6pt*)


StringyRandomReduction$X[6];(* first time to run this may takes a long time, following use would be much faster *)
Pause[3];(* error may occur without this pause *)%[[-1]]
Length[DeleteCases[%,0]]-1(* 6 master integral *)


StringyReductionDataFF$X[6,False]
Export["StringyIBPtoSolve6pt.mx",ffSparseSolve@@%[[1]]]
