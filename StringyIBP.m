(* ::Package:: *)

(************************ 0. Info and copyright ***********************)


StringyIBP$Version={"0.0.4","2024.1.10"};


(* Introduction to StringyIBP *)

(* To be completed...
*)


(* Update notes *)

(* 0.0.1  2023.6.7   Add Part I~III of this package.
   0.0.2  2023.6.27  Add Part IV for loop integrand.
   0.0.3  2023.8.30  Change default triangulation.
   0.0.4  2024.1.10  1.Add StringyReductionDataFF$X.
                     2.Use Options to specify certain parameters.
*)


(************************ 1. Begin package ***********************)


Print["Package StringyIBP version ",StringyIBP$Version[[1]],", ",StringyIBP$Version[[2]]];


(* Functions *)
ExtractVariableList::usage="ExtractVariableList[expr,var] gives all variables of form var[i] in expr. Here var can be a list like {var\:2081,var\:2082,...} (which gives all var\:2081[i],var\:2082[i],...).";
ParallelExpand::usage="ParallelExpand[expr,piecelength:500] parallelize Expand[expr] with piecelength terms in each kernel."
ParallelReplace::usage="ParallelReplace[expr,rules,levelspec:All,piecelength:500] parallelize Replace[expr,rules,levelspec] with piecelength terms in each kernel."


(* Data *)
Protect[X,c,y,u,int,intFF];


(* Conventions *)
$GlobalConventions$DeletedCij$=-1;
Protect[$GlobalConventions$DeletedCij$];


(************************ 2. Functions Part I ***********************)


Init[input_,default_]:=Switch[input,Null|Missing|{},default,_,input]


PassOptions[opts___,function_]:=Sequence@@Select[{opts},MemberQ[Options[function][[All,1]],#[[1]]]&]


LevelSpecQ[levelspec_]:=MatchQ[levelspec,All|Infinity|_Integer|{(_Integer|All|Infinity)...}]


ForgetEverything[]:=DeleteObject[PersistentObjects["Hashes/Once/*"]]


ExtractVariableList[expr_,var:Except[_List],sort_:(#&)]:=SortBy[Cases[{expr},_var,\[Infinity]]//DeleteDuplicates,sort]
ExtractVariableList[expr_,vars_List,sort_:(#&)]:=SortBy[Cases[{expr},Alternatives@@(Blank[#]&/@vars),\[Infinity]]//DeleteDuplicates,sort]
ExtractVariableFold[expr_,patt___]:=Fold[Switch[#2,_List,Cases[#1,Sequence@@#2],_,Cases[#1,#2,\[Infinity]]]&,expr,List@patt]


ExtractVarSubscript[expr_,var:Except[_List],sort_:(#&)]:=SortBy[Cases[{expr},Subscript[var,__],\[Infinity]]//DeleteDuplicates,sort]
ExtractVarSubscript[expr_,vars_List,sort_:(#&)]:=SortBy[Cases[{expr},Alternatives@@(Subscript[#,__]&/@vars),\[Infinity]]//DeleteDuplicates,sort]


Options[ParallelExpand]={"PieceLength"->500,Method->"CoarsestGrained"};
ParallelExpand[expr_Plus,OptionsPattern[Options[ParallelExpand]]]:=With[{piecelength=OptionValue["PieceLength"]},Module[{progress=0},SetSharedVariable[progress];
Monitor[Plus@@ParallelTable[(progress++;Expand[expr[[piecelength i+1;;Min[piecelength(i+1),expr//Length]]]]),{i,0,Ceiling[Length[expr]/piecelength]-1},Method->OptionValue[Method]],
ToString[progress]<>"/"<>ToString[Ceiling[Length[expr]/piecelength]]<>" terms have been expanded."]]]


Options[ParallelReplace]={"PieceLength"->500,Method->"CoarsestGrained"};
ParallelReplace[expr:_List|_Integer,rules_,Optional[levelspec_?LevelSpecQ,All],OptionsPattern[Options[ParallelReplace]]]:=With[{piecelength=OptionValue["PieceLength"]},Module[{progress=0,output},SetSharedVariable[progress];
output=Monitor[ParallelTable[(progress++;Replace[expr[[piecelength i+1;;Min[piecelength(i+1),expr//Length]]],Dispatch[rules],levelspec]),{i,0,Ceiling[Length[expr]/piecelength]-1},Method->OptionValue[Method]],
ToString[progress]<>"/"<>ToString[Ceiling[Length[expr]/piecelength]]<>" terms have been replaced."];
If[Head[expr]===Plus,Plus@@output,output]]]


(************************ 3. Functions Part II ***********************)


SetGlobalConventions["deleted cij"->n_Integer]:=(Unprotect[$GlobalConventions$DeletedCij$];Set[$GlobalConventions$DeletedCij$,n];Protect[$GlobalConventions$DeletedCij$];Print["Done."];)


Options[Xtri$Default]={"X"->X};
Xtri$Default[n_,OptionsPattern[Options[Xtri$Default]]]:=With[{X=OptionValue["X"],adj=Mod[{-1,0,1}-$GlobalConventions$DeletedCij$,n,1]},Table[Subscript[X,j,adj[[2]]],{j,Complement[Range[n],adj]}]/.Subscript[X,i_,j_]/;i>j:>Subscript[X,j,i]//Sort]


Options[Xvars]={"X"->X};
Options[Xcvars]={"X"->X,"c"->c,"Triangulation"->{}};
Xvars[n_,OptionsPattern[Options[Xvars]]]:=With[{X=OptionValue["X"]},DeleteCases[Table[Subscript[X,a,b],{a,1,n},{b,a+2,n}]//Flatten,Subscript[X,1,n]]]
Xcvars[n_,opts:OptionsPattern[Options[Xcvars]]]:=With[{X=OptionValue["X"],c=OptionValue["c"],Xi=Init[OptionValue["Triangulation"],Xtri$Default[n,PassOptions[opts,Xtri$Default]]],del$c=$GlobalConventions$DeletedCij$},Join[Xi,Sort[Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]]]]]


Options[Xcal]={"X"->X};
Options[ctoX]={"X"->X,"c"->c};
Options[Xtoc]={"X"->X,"c"->c,"Triangulation"->{}};
Xcal[n_,OptionsPattern[Options[Xcal]]]:=With[{X=OptionValue["X"]},{Subscript[X,i_,j_]:>Subscript[X,j,i]/;i>j,Subscript[X,i_,j_]/;i>n||j>n:>Subscript[X,Mod[i,n,1],Mod[j,n,1]],Subscript[X,i_,j_]/;j==i+1->0,Subscript[X,1,n]->0}]
ctoX[n_,opts:OptionsPattern[Options[ctoX]]]:=With[{X=OptionValue["X"],c=OptionValue["c"]},{Subscript[c,i_,j_]:>(Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n,PassOptions[opts,Xcal]])}]
Xtoc[n_,opts:OptionsPattern[Options[Xtoc]]]:=Once[With[{X=OptionValue["X"]},Solve[(#==(#/.ctoX[n,PassOptions[opts,ctoX]]))&/@Xcvars[n,opts],Complement[Xvars[n,"X"->X],Xcvars[n,opts]]][[1]]]]


Options[int$XctoX]={"Triangulation"->{}};
Options[int$XtoXc]={"Triangulation"->{}};
int$XctoX[expr_,OptionsPattern[Options[int$XctoX]]]:=(expr/.{integral_int:>Module[{n=(3+Sqrt[9+8 Length[integral]])/2},With[{Xtri="Triangulation"->Init[OptionValue["Triangulation"],Xtri$Default[n]]},
int@@Xvars[n]/.Xtoc[n,Xtri]/.Rule@@@({Xcvars[n,Xtri],List@@integral}\[Transpose])/.ctoX[n]]]})
int$XtoXc[expr_,OptionsPattern[Options[int$XtoXc]]]:=(expr/.{integral_int:>Module[{n=(3+Sqrt[9+8 Length[integral]])/2},With[{Xtri="Triangulation"->Init[OptionValue["Triangulation"],Xtri$Default[n]]},
int@@Xcvars[n,Xtri]/.ctoX[n]/.Rule@@@({Xvars[n],List@@integral}\[Transpose])/.Xtoc[n,Xtri]]]})


XctoPattern={Subscript[X,i_,j_]:>ToExpression["X"<>ToString[i]<>ToString[j]<>"_"],Subscript[c,i_,j_]:>ToExpression["c"<>ToString[i]<>ToString[j]<>"_"]};
XctoVarName={Subscript[X,i_,j_]:>ToExpression["X"<>ToString[i]<>ToString[j]],Subscript[c,i_,j_]:>ToExpression["c"<>ToString[i]<>ToString[j]]};
XctoPatternIf[Xij_Subscript,cond_]:=Prepend[XctoPattern,Xij:>ToExpression[StringJoin[#,"_Plus/;MemberQ[",#,",_Integer?(",ToString[cond],")]"]&@(ToString/@List@@Xij)]]


XctoStdOrd={expr_int:>SortBy[expr,Xcab|->Switch[#,Subscript[X,__],10#[[2]]+#[[3]],Subscript[c,__],1000#[[2]]+100#[[3]]]&@ExtractVarSubscript[Xcab,{X,c}][[1]]]};
Xc$cyclicPerm[expr_,n_,k_]:=Nest[(#/.{Subscript[X,a_,b_]:>Subscript[X,Mod[a+1,n,1],Mod[b+1,n,1]],Subscript[c,a_,b_]:>Subscript[c,Mod[a+1,n,1],Mod[b+1,n,1]]}/.
{Subscript[X,a_,b_]:>Subscript[X,b,a]/;a>b,Subscript[c,a_,b_]:>Subscript[c,b,a]/;a>b})&,expr,k]/.XctoStdOrd


Options[intXshift$cutoff]={"cutoff"->{1,True}};
intXshift$cutoff[inteq_,OptionsPattern[Options[intXshift$cutoff]]]:=With[{k=OptionValue["cutoff"][[1]],tag=OptionValue["cutoff"][[2]]},
If[TrueQ@tag,Max[Count[#,k+1+Subscript[X,__],\[Infinity]]&/@Cases[inteq,_int,\[Infinity]]]<=1&&FreeQ[inteq,int[___,Subscript[X,__]+m_Integer/;m<0||m>k+1,___]],FreeQ[inteq,int[___,Subscript[X,__]+m_Integer/;m<0||m>k,___]]]]
intXshift$sort[inteq_]:=With[{shifts=Abs[List@@@DeleteCases[Cases[{inteq},_int,\[Infinity]],Subscript[X,__],\[Infinity]]]},{Max@@Plus@@@shifts,Max@@Max@@@shifts,Plus@@Flatten[shifts],Plus@@Flatten[shifts]}]


Options[SelectStringyEquations$noshift]={"Triangulation"->{}};
SelectStringyEquations$noshift[eqs_,opts:OptionsPattern[Options[SelectStringyEquations$noshift]]]:=With[{n=(3+Sqrt[9+8 Length[ExtractVariableList[eqs,int][[1]]]])/2},
Select[eqs,Intersection[Table[#[[1]]/.Xij->Xij-1,{Xij,If[MemberQ[eqs,int[___,Subscript[c,__],___],\[Infinity]],Xcvars[n,opts],Xvars[n]]}],eqs[[;;,1]]]==={}&]]
SelectStringyEquations$AscendX[eqs_List,Xij_]:=With[{n=(3+Sqrt[9+8 Length[ExtractVariableList[eqs,int][[1]]]])/2},SortBy[Select[eqs,FreeQ[#[[2]],int[___,Xij,___]]&],intXshift$sort[#[[2]]]&]]


Options[utoyRules]={"Triangulation"->{}};
utoyRules[n_,OptionsPattern[Options[utoyRules]]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],del$c=$GlobalConventions$DeletedCij$},
Module[{xvar=Complement[Xvars[n],Xi],cvar=Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]],sol,ytou,ueqs},
sol=Solve[(cvar/.Subscript[c,i_,j_]:>Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n])==0,xvar][[1]]/.X->u;
ytou=Table[Subscript[y,i]==#[[i]]Product[sol[[j,1]]^Coefficient[sol[[j,2]],#[[i]]],{j,1,Length@sol}],{i,1,Length@#}]&@(Xi/.X->u);
ueqs=Table[uij/.Subscript[u,i_,j_]:>(1-Subscript[u,i,j]==Product[Subscript[u,k,l],{k,i+1,j-1},{l,Range[i-1]~Join~Range[j+1,n]}])/.
{Subscript[u,i_,j_]/;Abs[j-i]<=1->1}/.Subscript[u,i_,j_]/;i>j:>Subscript[u,j,i],{uij,Xvars[n,"X"->u]}];
Solve[ytou~Join~ueqs,Xvars[n,"X"->u]][[1]]]]]


Options[ytozRules]={"Triangulation"->{}};
ytozRules[n_,OptionsPattern[Options[ytozRules]]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],del$c=$GlobalConventions$DeletedCij$},Module[{xvar=Complement[Xvars[n],Xi],
cvar=Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]],sol,ytou,ueqs},
sol=Solve[(cvar/.Subscript[c,i_,j_]:>Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n])==0,xvar][[1]]/.X->u;
ytou=Table[Subscript[y,i]->#[[i]]Product[sol[[j,1]]^Coefficient[sol[[j,2]],#[[i]]],{j,1,Length@sol}],{i,1,Length@#}]&@(Xi/.X->u);
ytou/.Subscript[u,i_,j_]:>(Subscript[z,i-1]-Subscript[z,j])(Subscript[z,i]-Subscript[z,j-1])/((Subscript[z,i]-Subscript[z,j])(Subscript[z,i-1]-Subscript[z,j-1]))/.Subscript[z,i_]:>Subscript[z,Mod[i,n,1]]//Cancel]]]


Options[StringyIntegrand$X]={"Triangulation"->{}};
Options[StringyIntegrand$Xc]={"Triangulation"->{}};
Options[StringyPolynomial]={"Triangulation"->{}};
StringyIntegrand$X[n_,opts:OptionsPattern[Options[StringyIntegrand$X]]]:=PowerExpand[Product[Subscript[u,i,j]^Subscript[X,i,j],{i,n-2},{j,i+2,If[i==1,n-1,n]}]/Product[Subscript[y,i],{i,n-3}]/.utoyRules[n,opts]]
StringyIntegrand$Xc[n_,opts:OptionsPattern[Options[StringyIntegrand$Xc]]]:=PowerExpand[Product[Subscript[u,i,j]^Subscript[X,i,j],{i,n-2},{j,i+2,If[i==1,n-1,n]}]/Product[Subscript[y,i],{i,n-3}]/.utoyRules[n,opts]/.Xtoc[n,opts]]
StringyPolynomial[n_,i_,j_,opts:OptionsPattern[Options[StringyIntegrand$Xc]]]:=Once[Times@@Cases[StringyIntegrand$Xc[n,opts],_^-Subscript[c,i,j]][[;;,1]]]


(************************ 4. Functions Part III ***********************)


Options[TrivialIdentity$Xc]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
Options[TrivialIdentity$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
TrivialIdentity$Xc[n_,i_,j_,OptionsPattern[Options[TrivialIdentity$Xc]]]:=With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],p=OptionValue["F Polynomial"]},
With[{getRules=(expr|->Array[Xi[[#]]->Xi[[#]]+Exponent[expr,Subscript[y,#]]&,n-3]),intXc=int@@Xcvars[n,"Triangulation"->Xi],toList=(Switch[#,_Plus,List@@#,0,{},_,{#}]&),Xtri="Triangulation"->Xi},
If[p[n,i,j,Xtri]=!=1,intXc-Plus@@((intXc/.getRules[#]&)/@(toList@Expand@p[n,i,j,Xtri])/.Subscript[c,i,j]->Subscript[c,i,j]+1),0]]]
TrivialIdentity$X[n_,i_,j_,opts:OptionsPattern[Options[TrivialIdentity$X]]]:=int$XctoX[TrivialIdentity$Xc[n,i,j,opts],PassOptions[opts,int$XctoX]]


Options[IBP$Identity$Xc]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
Options[IBP$Identity$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
IBP$Identity$Xc[n_,k_,opts:OptionsPattern[Options[IBP$Identity$Xc]]]:=With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],p=OptionValue["F Polynomial"]},
With[{getRules=(expr|->Array[Xi[[#]]->Xi[[#]]+Exponent[expr,Subscript[y,#]]&,n-3]),intXc=int@@Xcvars[n,"Triangulation"->Xi],toList=(Switch[#,_Plus,List@@#,0,{},_,{#}]&),Xtri="Triangulation"->Xi},
If[1<=k<=n-3,Xi[[k]]intXc-Sum[Subscript[c,i,j]Plus@@((intXc/.getRules[#]&)/@(toList@Expand@D[p[n,i,j,Xtri],Subscript[y,k]])/.{Xi[[k]]->Xi[[k]]+1,Subscript[c,i,j]->Subscript[c,i,j]+1}),{i,1,n},{j,i,n}],Print["1\[LessEqual]k\[LessEqual]n-3?"]]//Expand]]
IBP$Identity$X[n_,k_,opts:OptionsPattern[Options[IBP$Identity$X]]]:=int$XctoX[IBP$Identity$Xc[n,k,opts],PassOptions[opts,int$XctoX]]/.ctoX[n]


Options[CheckStringyIdentity]={"Triangulation"->{}};
CheckStringyIdentity[id_,opts:OptionsPattern[Options[CheckStringyIdentity]]]:=With[{n=(3+Sqrt[9+8 Length[Cases[id,_int,\[Infinity]][[1]]]])/2,IBPtag=Cases[id//Simplify,_int*Subscript[X,__],\[Infinity]]},With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],
intXRule=RuleDelayed@@{int@@Xvars[n]/.XctoPattern,StringyIntegrand$X[n,opts]/.XctoVarName}},With[{intXcRule=RuleDelayed@@{int@@Xcvars[n,opts]/.XctoPattern,StringyIntegrand$Xc[n,opts]/.XctoVarName},yi=Subscript[y,Position[Xi,#][[1,1]]]&},
If[MemberQ[id,int[___,Subscript[c,__]],\[Infinity]],(id/.intXcRule)-If[IBPtag=!={},D[yi@IBPtag[[1,-1]]StringyIntegrand$Xc[n,opts],yi@IBPtag[[1,-1]]],0],
(id/.intXRule)-If[IBPtag=!={},D[yi@IBPtag[[1,-1]]StringyIntegrand$X[n,opts],yi@IBPtag[[1,-1]]],0]]==0//Simplify]]]


Options[StringyIdentity$X]={"Triangulation"->{}};
Options[StringyIdentity$Xc]={"Triangulation"->{}};
Options[StringyIdentity$X$shift]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
Options[StringyIdentity$X$All]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
StringyIdentity$X[n_,opts:OptionsPattern[Options[StringyIdentity$X]]]:=Once[DeleteCases[Flatten[Table[Expand@TrivialIdentity$X[n,i,j,opts]==0,{i,1,n},{j,i,n}]]~Join~Flatten[Table[Expand@IBP$Identity$X[n,k,opts]==0,{k,n-3}]],True]]
StringyIdentity$Xc[n_,opts:OptionsPattern[Options[StringyIdentity$Xc]]]:=Once[DeleteCases[Flatten[Table[Expand@TrivialIdentity$Xc[n,i,j,opts]==0,{i,1,n},{j,i,n}]]~Join~Flatten[Table[Expand@IBP$Identity$Xc[n,k,opts]==0,{k,n-3}]],True]]
StringyIdentity$X$shift[n_,opts:OptionsPattern[Options[StringyIdentity$X$shift]]]:=Once[With[{k=OptionValue["cutoff"][[1]]},(#[[1]]-#[[2]])&/@FullSimplify[DeleteDuplicates[Select[Flatten@
Table[eq/.Apply[Rule,{Xvars[n],Xvars[n]+#}\[Transpose]&/@Tuples[Range[0,k],n (n-3)/2],{2}],{eq,StringyIdentity$X[n,PassOptions[opts,StringyIdentity$X]]}],intXshift$cutoff[#,PassOptions[opts,intXshift$cutoff]]&]]]]]
StringyIdentity$X$All[n_,opts:OptionsPattern[Options[StringyIdentity$X$All]]]:=Once[DeleteDuplicates[Table[Xc$cyclicPerm[Once[StringyIdentity$X$shift[n,opts]],n,m],{m,0,n-1}]//Flatten]]


Options[intXs$List]={"cutoff"->{1,True},"Sort Funtion"->intXshift$sort};
intXs$List[n_,opts:OptionsPattern[Options[intXs$List]]]:=Once[With[{k=OptionValue["cutoff"][[1]]},SortBy[Select[int@@@(Xvars[n]+#&/@Tuples[Range[0,k+1],n (n-3)/2]),intXshift$cutoff[#,PassOptions[opts,intXshift$cutoff]]&],OptionValue["Sort Funtion"]]]]


Options[StringyReductionDataFF$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Extra Equations"->{},"Sort Funtion"->intXshift$sort,"intFF"->intFF};
StringyReductionDataFF$X[n_,opts:OptionsPattern[Options[StringyReductionDataFF$X]]]:=With[{intXs=intXs$List[n,PassOptions[opts,intXs$List]],XctoVarName$FF=Dispatch[#->(#/.XctoVarName)&/@Xvars[n]],intFF=OptionValue["intFF"]},
With[{intXtoFF=Table[intXs[[$i]]->intFF[$i],{$i,Length[intXs]}]},{{Collect[#,_intFF]&/@(Join[#==0&/@StringyIdentity$X$All[n,PassOptions[opts,StringyIdentity$X$All]],List@@OptionValue["Extra Equations"]]/.Dispatch[intXtoFF]),Reverse[intXtoFF[[All,2]]],"Parameters"->Xvars[n],"VarsPattern"->(Union[Cases[{#},_intFF,Infinity]]&)},Reverse/@intXtoFF}/.XctoVarName$FF]]


Options[StringyReduction$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Funtion"->intXshift$sort};
Options[StringyRelations$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Funtion"->intXshift$sort};
StringyReduction$X[n_,opts:OptionsPattern[Options[StringyReduction$X]]]:=Once[DeleteCases[RowReduce[Once[Reverse[Coefficient[#,intXs$List[n,PassOptions[opts,intXs$List]]]]&/@StringyIdentity$X$All[n,PassOptions[opts,StringyIdentity$X$All]]]]//Simplify,{0..}]]
StringyRelations$X[n_,opts:OptionsPattern[Options[StringyRelations$X]]]:=Once[(coeff|->FirstCase[#,{1,_}][[2]]==-Plus@@Times@@@Cases[#,Except[{0,_}]][[2;;]]&@({coeff,Reverse[intXs$List[n,PassOptions[opts,intXs$List]]]}\[Transpose]))/@StringyReduction$X[n,opts]]


Options[StringyAscendRules$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
Options[StringyDescendRules$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Funtion"->intXshift$sort};
StringyAscendRules$X[n_,opts:OptionsPattern[Options[StringyAscendRules$X]]]:=Once[Table[RuleDelayed@@{#[[1]]/.XctoPatternIf[Xij,Negative],#[[2]]/.XctoVarName}&@SelectStringyEquations$AscendX[Equal@@Solve[#,int@@Xvars[n]][[1,1]]&/@
Select[#==0&/@StringyIdentity$X$All[n,opts],MemberQ[#,int@@Xvars[n],\[Infinity]]&],Xij][[1]],{Xij,Xvars[n]}]]
StringyDescendRules$X[n_,opts:OptionsPattern[Options[StringyDescendRules$X]]]:=Once[(RuleDelayed@@{#1[[1]]/.#2/.XctoPatternIf[#2[[1,1]],(m|->(#>m&))[#3]],#1[[2]]/.#2/.XctoVarName}&)@@@
(Append[#,Max[ExtractVariableFold[#[[1,2]],_int,#[[2,1,1]]+_,{_Integer,2}],0]]&@*(eq|->{eq,(#[[2]]->#[[2]]-#[[1]]&@*Sort/@List@@@Cases[eq[[1]],Subscript[X,__]+_])})/@
SelectStringyEquations$noshift[StringyRelations$X[n,opts],PassOptions[opts,SelectStringyEquations$noshift]])]


Options[StringyRandomReduction$X]={"Triangulation"->{},"cutoff"->{1,False},"F Polynomial"->StringyPolynomial,"Max Range"->10,"Precision"->10^-10};
StringyRandomReduction$X[n_,opts:OptionsPattern[Options[StringyRandomReduction$X]]]:=With[{ranMax=OptionValue["Max Range"],dx=OptionValue["Precision"]},DeleteCases[Rationalize[RowReduce[Once[Reverse[Coefficient[#,intXs$List[n,PassOptions[opts,intXs$List]]]]&/@
StringyIdentity$X$All[n,PassOptions[opts,StringyIdentity$X$All]]]/.Table[Xij->RandomReal[{-ranMax,ranMax}],{Xij,Xvars[n]}]],dx],{0..}]]


(************************ 5. Functions Part IV ***********************)


FeynGraph$1Loop[n_]:=Once[Graph[Join[Table[Labeled[Subscript["V",i]\[UndirectedEdge]Subscript["V",Mod[i-1,n,1]],Subscript["y",i]],{i,n}],Table[Subscript["p",i]\[UndirectedEdge]Subscript["V",i],{i,n}]],VertexLabels->"Name"]]


uPath[n_Integer,i_Integer,j_Integer]:=Once[If[i!=j,Cases[FindPath[FeynGraph[n],Subscript["p",i],Subscript["p",j],\[Infinity],All],{___,Subscript["V",a_],Subscript["V",b_],___}/;b==a+1][[1]],
If[FreeQ[#,{___,Subscript["V",a_],Subscript["V",b_],___}/;b==a+1],Reverse[#],#]&@Join[{Subscript["p",i]},RotateLeft[#,Position[#,Subscript["V",i]\[UndirectedEdge]_][[1,1]]-1]&@
FindCycle[{FeynGraph$1Loop[n],Subscript["V",i]},\[Infinity],All][[1]]/.UndirectedEdge->Sequence,{Subscript["p",i]}]//.{a___,b_,b_,c___}:>{a,b,c}]]


uijPolynomial[n_Integer,i_Integer,j_Integer]:=Once[#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&@(Dot@@Table[{#[[k-1]],#[[k]]}/.{{Subscript["V",a_],Subscript["p",_]}:>{{Subscript[y,a],Subscript[y,a]},{0,1}},
{Subscript["V",a_],Subscript["V",b_]}:>{{Subscript[y,a],0},{1,1}},{Subscript["p",a_],Subscript["V",_]}:>{{1,1},{0,1}}},{k,2,Length[#]}]&@Delete[uPath[n,i,j],2])]


uYiPolynomial[n_Integer,i_Integer,tilde_Integer]:=Once[#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&@If[tilde>0,Dot@@Table[{#[[k-1]],#[[k]]}/.{{Subscript["V",a_],Subscript["p",_]}:>{{Subscript[y,a],0},{1,1}},
{Subscript["V",a_],Subscript["V",b_]}:>{{Subscript[y,a],0},{1,1}},{Subscript["p",a_],Subscript["V",_]}:>{{1,1},{0,1}}},{k,2,Length[#]}]&@Delete[uPath[n,i,i],2],
Dot@@Table[{#[[k-1]],#[[k]]}/.{{Subscript["V",a_],Subscript["p",_]}:>{{Subscript[y,a],Subscript[y,a]},{0,1}},{Subscript["V",a_],Subscript["V",b_]}:>{{Subscript[y,a],Subscript[y,a]},{0,1}},
{Subscript["p",a_],Subscript["V",_]}:>{{1,0},{1,1}}},{k,2,Length[#]}]&@Reverse[Delete[uPath[n,i,i],2]]]]


StringyIntegrand$XY[n_]:=Once[PowerExpand[Product[If[Mod[i,n]+1==j,1,uijPolynomial[n,i,j]^Subscript[X,i,j]],{i,n},{j,n}]Product[uYiPolynomial[n,i,tag]^Subscript[If[tag>0,Y,\!\(\*
TagBox[
StyleBox[
RowBox[{"OverTilde", "[", "Y", "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)],i],{i,n},{tag,{1,-1}}]/.a_Plus:>Factor[a]]]


(*StringyIBP$5pt[expr_]:=Module[{AscendRules={
int[X13_Plus/;MemberQ[X13,_Integer?Negative],X14_,X24_,X25_,X35_]\[RuleDelayed]((X13-X14+X24) int[1+X13,X14,X24,X25,X35]+(X14-X24+X25) int[1+X13,1+X14,X24,X25,X35])/X13,
int[X13_,X14_Plus/;MemberQ[X14,_Integer?Negative],X24_,X25_,X35_]\[RuleDelayed]((X14-X24+X25) int[X13,1+X14,X24,X25,X35]+(X24-X25+X35) int[X13,1+X14,1+X24,X25,X35])/X14,
int[X13_,X14_,X24_Plus/;MemberQ[X24,_Integer?Negative],X25_,X35_]\[RuleDelayed]((X24-X25+X35) int[X13,X14,1+X24,X25,X35]+(X13+X25-X35) int[X13,X14,1+X24,1+X25,X35])/X24,
int[X13_,X14_,X24_,X25_Plus/;MemberQ[X25,_Integer?Negative],X35_]\[RuleDelayed]((X13+X25-X35) int[X13,X14,X24,1+X25,X35]+(-X13+X14+X35) int[X13,X14,X24,1+X25,1+X35])/X25,
int[X13_,X14_,X24_,X25_,X35_Plus/;MemberQ[X35,_Integer?Negative]]\[RuleDelayed]((-X13+X14+X35) int[X13,X14,X24,X25,1+X35]+(X13-X14+X24) int[1+X13,X14,X24,X25,1+X35])/X35},
DescendRules={
int[X13_,X14_,X24_,X25_,X35_Plus/;MemberQ[X35,_Integer?(#1>1&)]]\[RuleDelayed]((1+X13+X25-X35) (-2+X35) int[X13,X14,X24,X25,-2+X35])/((-1-X13+X14+X35) (-1+X24-X25+X35))+((1+X24-X25-X13 (1+X24-X25+2 (-2+X35))+3 (-2+X35)+X24 (-2+X35)-2 X25 (-2+X35)+2 (-2+X35)^2+X14 (-1-X25+X35)) int[X13,X14,X24,X25,-1+X35])/((-1-X13+X14+X35) (-1+X24-X25+X35)),
int[X13_Plus/;MemberQ[X13,_Integer?(#1>0&)],X14_,X24_,X25_,X35_]\[RuleDelayed]-(((-(-1+X13)^2+(-1+X13) (X14-X24)+X35 (X24-X25+X35)) int[-1+X13,X14,X24,X25,X35])/((-1+X13-X14+X24) (-1+X13+X25-X35)))-((-1+X13-X14-X35) (X24-X25+X35) int[-1+X13,X14,X24,X25,1+X35])/((-1+X13-X14+X24) (-1+X13+X25-X35)),
int[X13_,X14_Plus/;MemberQ[X14,_Integer?(#1>0&)],X24_,X25_,X35_]\[RuleDelayed]-(((1-X14+X24-X25+X35) int[X13,-1+X14,X24,X25,X35])/(-1+X14-X24+X25))+((X24-X25+X35) int[X13,-1+X14,X24,X25,1+X35])/(-1+X14-X24+X25),
int[X13_,X14_,X24_Plus/;MemberQ[X24,_Integer?(#1>0&)],X25_,X35_]\[RuleDelayed]-(((1-X13+X14-X24+X35) int[X13,X14,-1+X24,X25,X35])/(-1+X13-X14+X24))+((-X13+X14+X35) int[X13,X14,-1+X24,X25,1+X35])/(-1+X13-X14+X24),
int[X13_,X14_,X24_,X25_Plus/;MemberQ[X25,_Integer?(#1>0&)],X35_]\[RuleDelayed]-(((X24 (-1+X25)-(-1+X25)^2-X13 X35+X35^2+X14 (1-X25+X35)) int[X13,X14,X24,-1+X25,X35])/((-1+X14-X24+X25) (-1+X13+X25-X35)))+((-X13+X14+X35) (1+X24-X25+X35) int[X13,X14,X24,-1+X25,1+X35])/((-1+X14-X24+X25) (-1+X13+X25-X35))},
FullSimplify/@simplify[Simplify/@simplify[expr//.AscendRules]//.DescendRules]]*)
