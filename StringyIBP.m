(* ::Package:: *)

(************************ 0. Info and copyright ***********************)


StringyIBP$Version={"0.0.6","2024.5.7"};


(* Introduction to StringyIBP *)

(* To be completed...
*)


(* Update notes *)

(* 0.0.1  2023.6.7   Add Part I~III of this package.
   0.0.2  2023.6.27  Add Part IV for loop integrand.
   0.0.3  2023.8.30  Change default triangulation.
   0.0.4  2024.1.10  1.Add StringyReductionDataFF$X.
                     2.Use Options to specify certain parameters.
   0.0.5  2024.4.25  1.Add scaffolding.
                     2.Use Dn\[Infinity] instead of Dn.
   0.0.6  2024.5.7   1.Add Parke-Taylor form.
                     2.Rewrite Options passing.
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


PassOptions[opts___Rule,func1_,func2_]:=Sequence@@FilterRules[Normal[Merge[{opts,Options[func1]},First]],Options[func2]]


LevelSpecQ[levelspec_]:=MatchQ[levelspec,All|Infinity|_Integer|{(_Integer|All|Infinity)...}]


ForgetEverything[]:=DeleteObject[PersistentObjects["Hashes/Once/*"]]


ExtractVariableList[expr_,var:Except[_List],sort_:(#&)]:=SortBy[Cases[{expr},_var,\[Infinity]]//DeleteDuplicates,sort]
ExtractVariableList[expr_,vars_List,sort_:(#&)]:=SortBy[Cases[{expr},Alternatives@@(Blank[#]&/@vars),\[Infinity]]//DeleteDuplicates,sort]
ExtractVariableFold[expr_,patt___]:=Fold[Switch[#2,_List,Cases[#1,Sequence@@#2],_,Cases[#1,#2,\[Infinity]]]&,expr,List@patt]


ExtractVarSubscript[expr_,var:Except[_List],sort_:(#&)]:=SortBy[Cases[{expr},Subscript[var,__],\[Infinity]]//DeleteDuplicates,sort]
ExtractVarSubscript[expr_,vars_List,sort_:(#&)]:=SortBy[Cases[{expr},Alternatives@@(Subscript[#,__]&/@vars),\[Infinity]]//DeleteDuplicates,sort]


Options[ParallelExpand]={"PieceLength"->500,Method->"CoarsestGrained"};
ParallelExpand[expr_Plus,OptionsPattern[]]:=With[{piecelength=OptionValue["PieceLength"]},Module[{progress=0},SetSharedVariable[progress];
Monitor[Plus@@ParallelTable[(progress++;Expand[expr[[piecelength i+1;;Min[piecelength(i+1),expr//Length]]]]),{i,0,Ceiling[Length[expr]/piecelength]-1},Method->OptionValue[Method]],
ToString[progress]<>"/"<>ToString[Ceiling[Length[expr]/piecelength]]<>" terms have been expanded."]]]


Options[ParallelReplace]={"PieceLength"->500,Method->"CoarsestGrained"};
ParallelReplace[expr:_List|_Integer,rules_,Optional[levelspec_?LevelSpecQ,All],OptionsPattern[]]:=With[{piecelength=OptionValue["PieceLength"]},Module[{progress=0,output},SetSharedVariable[progress];
output=Monitor[ParallelTable[(progress++;Replace[expr[[piecelength i+1;;Min[piecelength(i+1),expr//Length]]],Dispatch[rules],levelspec]),{i,0,Ceiling[Length[expr]/piecelength]-1},Method->OptionValue[Method]],
ToString[progress]<>"/"<>ToString[Ceiling[Length[expr]/piecelength]]<>" terms have been replaced."];
If[Head[expr]===Plus,Plus@@output,output]]]


(************************ 3. Functions Part II ***********************)


SetGlobalConventions["deleted cij"->n_Integer]:=(Unprotect[$GlobalConventions$DeletedCij$];Set[$GlobalConventions$DeletedCij$,n];Protect[$GlobalConventions$DeletedCij$];Print["Done."];)


Options[Xtri$Default]={"X"->X};
Xtri$Default[n_,OptionsPattern[]]:=With[{X=OptionValue["X"],adj=Mod[{-1,0,1}-$GlobalConventions$DeletedCij$,n,1]},Table[Subscript[X,j,adj[[2]]],{j,Complement[Range[n],adj]}]/.Subscript[X,i_,j_]/;i>j:>Subscript[X,j,i]//Sort]


Options[Xvars]={"X"->X};
Options[Xcvars]={"X"->X,"c"->c,"Triangulation"->{}};
Xvars[n_,OptionsPattern[]]:=With[{X=OptionValue["X"]},DeleteCases[Table[Subscript[X,a,b],{a,1,n},{b,a+2,n}]//Flatten,Subscript[X,1,n]]]
Xcvars[n_,opts:OptionsPattern[]]:=With[{X=OptionValue["X"],c=OptionValue["c"],Xi=Init[OptionValue["Triangulation"],Xtri$Default[n,Sequence@@FilterRules[{opts},Options[Xtri$Default]]]],del$c=$GlobalConventions$DeletedCij$},Join[Xi,Sort[Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]]]]]


Options[Xcal]={"X"->X};
Options[ctoX]={"X"->X,"c"->c};
Options[Xtoc]={"X"->X,"c"->c,"Triangulation"->{}};
Xcal[n_,OptionsPattern[]]:=With[{X=OptionValue["X"]},{Subscript[X,i_,j_]:>Subscript[X,j,i]/;i>j,Subscript[X,i_,j_]/;i>n||j>n:>Subscript[X,Mod[i,n,1],Mod[j,n,1]],Subscript[X,i_,j_]/;j==i+1->0,Subscript[X,1,n]->0}]
ctoX[n_,opts:OptionsPattern[]]:=With[{X=OptionValue["X"],c=OptionValue["c"]},{Subscript[c,i_,j_]:>(Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n,Sequence@@FilterRules[{opts},Options[Xcal]]])}]
Xtoc[n_,opts:OptionsPattern[]]:=Once[With[{X=OptionValue["X"]},Solve[(#==(#/.ctoX[n,Sequence@@FilterRules[{opts},Options[ctoX]]]))&/@Xcvars[n,opts],Complement[Xvars[n,"X"->X],Xcvars[n,opts]]][[1]]]]


Options[stoXcRules]={"Triangulation"->{}};
stoXRules[n_]:=Solve[Join[Table[Sum[Subscript[s,i,j],{j,n}]==0/.{Subscript[s,i_,j_]/;i>j:>Subscript[s,j,i],Subscript[s,i_,i_]->0},{i,n}],Xvars[n]/.{Subscript[X,i_,j_]:>Subscript[X,i,j]==Sum[Subscript[s,a,b],{a,i,j-1},{b,a,j-1}]}/.{Subscript[s,i_,j_]/;i>j:>Subscript[s,j,i],Subscript[s,i_,i_]->0}],Flatten@Table[Subscript[s,i,j],{i,n},{j,i+1,n}]][[1]]
stoXcRules[n_,opts:OptionsPattern[]]:=Solve[Join[Table[Sum[Subscript[s,i,j],{j,n}]==0/.{Subscript[s,i_,j_]/;i>j:>Subscript[s,j,i],Subscript[s,i_,i_]->0},{i,n}],Xcvars[n,opts]/.{Subscript[X,i_,j_]:>Subscript[X,i,j]==Sum[Subscript[s,a,b],{a,i,j-1},{b,a,j-1}],Subscript[c,i_,j_]:>Subscript[c,i,j]==-Subscript[s,i,j]}/.{Subscript[s,i_,j_]/;i>j:>Subscript[s,j,i],Subscript[s,i_,i_]->0}],Flatten@Table[Subscript[s,i,j],{i,n},{j,i+1,n}]][[1]]


Options[int$XctoX]={"Triangulation"->{}};
Options[int$XtoXc]={"Triangulation"->{}};
int$XctoX[expr_,OptionsPattern[]]:=(expr/.{integral_int:>Module[{n=(3+Sqrt[9+8 Length[integral]])/2},With[{Xtri="Triangulation"->Init[OptionValue["Triangulation"],Xtri$Default[n]]},
int@@Xvars[n]/.Xtoc[n,Xtri]/.Rule@@@({Xcvars[n,Xtri],List@@integral}\[Transpose])/.ctoX[n]]]})
int$XtoXc[expr_,OptionsPattern[]]:=(expr/.{integral_int:>Module[{n=(3+Sqrt[9+8 Length[integral]])/2},With[{Xtri="Triangulation"->Init[OptionValue["Triangulation"],Xtri$Default[n]]},
int@@Xcvars[n,Xtri]/.ctoX[n]/.Rule@@@({Xvars[n],List@@integral}\[Transpose])/.Xtoc[n,Xtri]]]})


XctoPattern={Subscript[X,i_,j_]:>ToExpression["X"<>ToString[i]<>ToString[j]<>"_"],Subscript[c,i_,j_]:>ToExpression["c"<>ToString[i]<>ToString[j]<>"_"]};
XctoVarName={Subscript[X,i_,j_]:>ToExpression["X"<>ToString[i]<>ToString[j]],Subscript[c,i_,j_]:>ToExpression["c"<>ToString[i]<>ToString[j]]};
XctoPatternIf[Xij_Subscript,cond_]:=Prepend[XctoPattern,Xij:>ToExpression[StringJoin[#,"_Plus/;MemberQ[",#,",_Integer?(",ToString[cond],")]"]&@(ToString/@List@@Xij)]]


XctoStdOrd={expr_int:>SortBy[expr,Xcab|->Switch[#,Subscript[X,__],10#[[2]]+#[[3]],Subscript[c,__],1000#[[2]]+100#[[3]]]&@ExtractVarSubscript[Xcab,{X,c}][[1]]]};
Xc$cyclicPerm[expr_,n_,k_]:=Nest[(#/.{Subscript[X,a_,b_]:>Subscript[X,Mod[a+1,n,1],Mod[b+1,n,1]],Subscript[c,a_,b_]:>Subscript[c,Mod[a+1,n,1],Mod[b+1,n,1]]}/.
{Subscript[X,a_,b_]:>Subscript[X,b,a]/;a>b,Subscript[c,a_,b_]:>Subscript[c,b,a]/;a>b})&,expr,k]/.XctoStdOrd


Options[intXshift$cutoff]={"cutoff"->{1,True}};
intXshift$cutoff[inteq_,OptionsPattern[]]:=With[{k=OptionValue["cutoff"][[1]],tag=OptionValue["cutoff"][[2]]},
If[TrueQ@tag,Max[Count[#,k+1+Subscript[X,__],\[Infinity]]&/@Cases[inteq,_int,\[Infinity]]]<=1&&FreeQ[inteq,int[___,Subscript[X,__]+m_Integer/;m<0||m>k+1,___]],FreeQ[inteq,int[___,Subscript[X,__]+m_Integer/;m<0||m>k,___]]]]
intXshift$sort[inteq_]:=With[{shifts=Abs[List@@@DeleteCases[Cases[{inteq},_int,\[Infinity]],Subscript[X,__],\[Infinity]]]},{Max@@Plus@@@shifts,Max@@Max@@@shifts,Plus@@Flatten[shifts],Plus@@Flatten[shifts]}]


Options[SelectStringyEquations$noshift]={"Triangulation"->{}};
SelectStringyEquations$noshift[eqs_,opts:OptionsPattern[]]:=With[{n=(3+Sqrt[9+8 Length[ExtractVariableList[eqs,int][[1]]]])/2},
Select[eqs,Intersection[Table[#[[1]]/.Xij->Xij-1,{Xij,If[MemberQ[eqs,int[___,Subscript[c,__],___],\[Infinity]],Xcvars[n,opts],Xvars[n]]}],eqs[[;;,1]]]==={}&]]
SelectStringyEquations$AscendX[eqs_List,Xij_]:=With[{n=(3+Sqrt[9+8 Length[ExtractVariableList[eqs,int][[1]]]])/2},SortBy[Select[eqs,FreeQ[#[[2]],int[___,Xij,___]]&],intXshift$sort[#[[2]]]&]]


Options[utoyRules]={"Triangulation"->{}};
utoyRules[n_,OptionsPattern[]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],del$c=$GlobalConventions$DeletedCij$},
Module[{xvar=Complement[Xvars[n],Xi],cvar=Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]],sol,ytou,ueqs},
sol=Solve[(cvar/.Subscript[c,i_,j_]:>Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n])==0,xvar][[1]]/.X->u;
ytou=Table[Subscript[y,i]==#[[i]]Product[sol[[j,1]]^Coefficient[sol[[j,2]],#[[i]]],{j,1,Length@sol}],{i,1,Length@#}]&@(Xi/.X->u);
ueqs=Table[uij/.Subscript[u,i_,j_]:>(1-Subscript[u,i,j]==Product[Subscript[u,k,l],{k,i+1,j-1},{l,Range[i-1]~Join~Range[j+1,n]}])/.
{Subscript[u,i_,j_]/;Abs[j-i]<=1->1}/.Subscript[u,i_,j_]/;i>j:>Subscript[u,j,i],{uij,Xvars[n,"X"->u]}];
Solve[ytou~Join~ueqs,Xvars[n,"X"->u]][[1]]]]]


Options[ytozRules]={"Triangulation"->{}};
ytozRules[n_,OptionsPattern[]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],del$c=$GlobalConventions$DeletedCij$},Module[{xvar=Complement[Xvars[n],Xi],
cvar=Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]],sol,ytou,ueqs},
sol=Solve[(cvar/.Subscript[c,i_,j_]:>Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n])==0,xvar][[1]]/.X->u;
ytou=Table[Subscript[y,i]->#[[i]]Product[sol[[j,1]]^Coefficient[sol[[j,2]],#[[i]]],{j,1,Length@sol}],{i,1,Length@#}]&@(Xi/.X->u);
ytou/.Subscript[u,i_,j_]:>(Subscript[z,i-1]-Subscript[z,j])(Subscript[z,i]-Subscript[z,j-1])/((Subscript[z,i]-Subscript[z,j])(Subscript[z,i-1]-Subscript[z,j-1]))/.Subscript[z,i_]:>Subscript[z,Mod[i,n,1]]//Cancel]]]


Options[ztoyRules]={"Triangulation"->{},"Fix SL2"->"1,n-1,n"};
ztoyRules[n_,opts:OptionsPattern[]]:=With[{fixSL2=SortBy[Switch[OptionValue["Fix SL2"],"1,n-1,n",{Subscript[z,1]->0,Subscript[z,n-1]->1,Subscript[z,n]->\[Infinity]},"1,2,n",{Subscript[z,1]->0,Subscript[z,2]->1,Subscript[z,n]->\[Infinity]},_,OptionValue["Fix SL2"]],Count[#,\[Infinity],\[Infinity]]&]},
SortBy[Join[fixSL2,Solve[Map[Limit[#,fixSL2[[-1]]]&,ytozRules[n,Sequence@@FilterRules[{opts},Options[ytozRules]]]/.Rule->Equal/.fixSL2[[;;-2]],{2}],Complement[Table[Subscript[z,$i],{$i,n}],fixSL2[[;;,1]]]][[1]]//Factor],Count[#,\[Infinity],\[Infinity]]&]]


Options[StringyIntegrand$X]={"Triangulation"->{}};
Options[StringyIntegrand$Xc]={"Triangulation"->{}};
Options[StringyPolynomial]={"Triangulation"->{}};
StringyIntegrand$X[n_,opts:OptionsPattern[]]:=PowerExpand[Product[Subscript[u,i,j]^Subscript[X,i,j],{i,n-2},{j,i+2,If[i==1,n-1,n]}]/Product[Subscript[y,i],{i,n-3}]/.utoyRules[n,opts]]
StringyIntegrand$Xc[n_,opts:OptionsPattern[]]:=PowerExpand[Product[Subscript[u,i,j]^Subscript[X,i,j],{i,n-2},{j,i+2,If[i==1,n-1,n]}]/Product[Subscript[y,i],{i,n-3}]/.utoyRules[n,opts]/.Xtoc[n,opts]]
StringyPolynomial[n_,i_,j_,opts:OptionsPattern[]]:=Once[Times@@Cases[StringyIntegrand$Xc[n,opts],_^-Subscript[c,i,j]][[;;,1]]]


Options[intPT$Xc]={"Triangulation"->{},"Fix SL2"->"1,n-1,n"};
Options[intPT$X]={"Triangulation"->{},"Fix SL2"->"1,n-1,n"};
intPT$Xc[perm__Integer,opts:OptionsPattern[]]:=With[{PT=(Times@@({i,j}|->1/(Subscript[z,i]-Subscript[z,j]))@@@({{##},RotateLeft@{##}}\[Transpose])&),ztoy=ztoyRules[Length[{perm}],opts],n=Length[{perm}]},
With[{prefactor=Limit[PT[perm]/PT@@Range[n]/.ztoy[[;;-2]],ztoy[[-1]]]//Factor,shiftRules=SortBy[Rule@@@(List@@StringyIntegrand$Xc[n,Sequence@@FilterRules[{opts},Options[StringyIntegrand$Xc]]]/.Power->List/.{y_,Xc_Subscript+n_Integer}:>{y,Xc}/.{y_,-Xc_Subscript}:>{y,Xc^-1}),-LeafCount[#[[1]]]&],intXc=int@@Xcvars[n,Sequence@@FilterRules[{opts},Options[Xcvars]]]},
If[NumericQ[prefactor],prefactor intXc,If[Head[prefactor]===Times,Select[prefactor,FreeQ[#,Subscript[y,_]]&]intXc/.(Select[List@@prefactor,!FreeQ[#,Subscript[y,_]]&]/.shiftRules/.{Xc_Subscript:>(Xc->Xc+1),Xc_Subscript^n_:>(Xc->Xc+n)}),Print["Error."]]]]]
intPT$X[perm__Integer,opts:OptionsPattern[]]:=int$XctoX[intPT$Xc[perm,opts],Sequence@@FilterRules[{opts},Options[int$XctoX]]]
intX$PTshift$sort[inteq_]:=With[{n=(3+Sqrt[9+8 Length[Cases[{inteq},_int,\[Infinity]][[1]]]])/2},With[{intPTs=Once[Alternatives@@Union@Cases[intPT$X[1,Sequence@@#,n-1,n]&/@Permutations[Range[2,n-2]],_int,\[Infinity]]]},{Count[{inteq},Except[intPTs,_int],\[Infinity]],intXshift$sort[inteq]}]]


(************************ 4. Functions Part III ***********************)


Options[TrivialIdentity$Xc]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
Options[TrivialIdentity$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
TrivialIdentity$Xc[n_,i_,j_,OptionsPattern[]]:=With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],p=OptionValue["F Polynomial"]},
With[{getRules=(expr|->Array[Xi[[#]]->Xi[[#]]+Exponent[expr,Subscript[y,#]]&,n-3]),intXc=int@@Xcvars[n,"Triangulation"->Xi],toList=(Switch[#,_Plus,List@@#,0,{},_,{#}]&),Xtri="Triangulation"->Xi},
If[p[n,i,j,Xtri]=!=1,intXc-Plus@@((intXc/.getRules[#]&)/@(toList@Expand@p[n,i,j,Xtri])/.Subscript[c,i,j]->Subscript[c,i,j]+1),0]]]
TrivialIdentity$X[n_,i_,j_,opts:OptionsPattern[]]:=int$XctoX[TrivialIdentity$Xc[n,i,j,opts],Sequence@@FilterRules[{opts},Options[int$XctoX]]]


Options[IBP$Identity$Xc]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
Options[IBP$Identity$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
IBP$Identity$Xc[n_,k_,opts:OptionsPattern[]]:=With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],p=OptionValue["F Polynomial"]},
With[{getRules=(expr|->Array[Xi[[#]]->Xi[[#]]+Exponent[expr,Subscript[y,#]]&,n-3]),intXc=int@@Xcvars[n,"Triangulation"->Xi],toList=(Switch[#,_Plus,List@@#,0,{},_,{#}]&),Xtri="Triangulation"->Xi},
If[1<=k<=n-3,Xi[[k]]intXc-Sum[Subscript[c,i,j]Plus@@((intXc/.getRules[#]&)/@(toList@Expand@D[p[n,i,j,Xtri],Subscript[y,k]])/.{Xi[[k]]->Xi[[k]]+1,Subscript[c,i,j]->Subscript[c,i,j]+1}),{i,1,n},{j,i,n}],Print["1\[LessEqual]k\[LessEqual]n-3?"]]//Expand]]
IBP$Identity$X[n_,k_,opts:OptionsPattern[]]:=int$XctoX[IBP$Identity$Xc[n,k,opts],Sequence@@FilterRules[{opts},Options[int$XctoX]]]/.ctoX[n]


Options[CheckStringyIdentity]={"Triangulation"->{}};
CheckStringyIdentity[id_,opts:OptionsPattern[]]:=With[{n=(3+Sqrt[9+8 Length[Cases[id,_int,\[Infinity]][[1]]]])/2,IBPtag=Cases[id//Simplify,_int*Subscript[X,__],\[Infinity]]},With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],
intXRule=RuleDelayed@@{int@@Xvars[n]/.XctoPattern,StringyIntegrand$X[n,opts]/.XctoVarName}},With[{intXcRule=RuleDelayed@@{int@@Xcvars[n,opts]/.XctoPattern,StringyIntegrand$Xc[n,opts]/.XctoVarName},yi=Subscript[y,Position[Xi,#][[1,1]]]&},
If[MemberQ[id,int[___,Subscript[c,__]],\[Infinity]],(id/.intXcRule)-If[IBPtag=!={},D[yi@IBPtag[[1,-1]]StringyIntegrand$Xc[n,opts],yi@IBPtag[[1,-1]]],0],
(id/.intXRule)-If[IBPtag=!={},D[yi@IBPtag[[1,-1]]StringyIntegrand$X[n,opts],yi@IBPtag[[1,-1]]],0]]==0//Simplify]]]


Options[StringyIdentity$X]={"Triangulation"->{}};
Options[StringyIdentity$Xc]={"Triangulation"->{}};
Options[StringyIdentity$X$shift]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
Options[StringyIdentity$X$All]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
StringyIdentity$X[n_,opts:OptionsPattern[]]:=Once[DeleteCases[Flatten[Table[Expand@TrivialIdentity$X[n,i,j,opts]==0,{i,1,n},{j,i,n}]]~Join~Flatten[Table[Expand@IBP$Identity$X[n,k,opts]==0,{k,n-3}]],True]]
StringyIdentity$Xc[n_,opts:OptionsPattern[]]:=Once[DeleteCases[Flatten[Table[Expand@TrivialIdentity$Xc[n,i,j,opts]==0,{i,1,n},{j,i,n}]]~Join~Flatten[Table[Expand@IBP$Identity$Xc[n,k,opts]==0,{k,n-3}]],True]]
StringyIdentity$X$shift[n_,opts:OptionsPattern[]]:=Once[With[{k=OptionValue["cutoff"][[1]]},(#[[1]]-#[[2]])&/@FullSimplify[DeleteDuplicates[Select[Flatten@
Table[eq/.Apply[Rule,{Xvars[n],Xvars[n]+#}\[Transpose]&/@Tuples[Range[0,k],n (n-3)/2],{2}],{eq,StringyIdentity$X[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X]]]}],intXshift$cutoff[#,Sequence@@FilterRules[{opts},Options[intXshift$cutoff]]]&]]]]]
StringyIdentity$X$All[n_,opts:OptionsPattern[]]:=Once[DeleteDuplicates[Table[Xc$cyclicPerm[Once[StringyIdentity$X$shift[n,opts]],n,m],{m,0,n-1}]//Flatten]]


Options[intXs$List]={"cutoff"->{1,True},"Sort Function"->intX$PTshift$sort};
intXs$List[n_,opts:OptionsPattern[]]:=Once[With[{k=OptionValue["cutoff"][[1]]},SortBy[Select[int@@@(Xvars[n]+#&/@Tuples[Range[0,k+1],n (n-3)/2]),intXshift$cutoff[#,Sequence@@FilterRules[{opts},Options[intXshift$cutoff]]]&],OptionValue["Sort Function"]]]]


Options[StringyReductionDataFF$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Extra Equations"->{},"Sort Function"->intX$PTshift$sort,"intFF"->intFF};
StringyReductionDataFF$X[n_,opts:OptionsPattern[]]:=With[{intXs=intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]],XctoVarName$FF=Dispatch[#->(#/.XctoVarName)&/@Xvars[n]],intFF=OptionValue["intFF"]},
With[{intXtoFF=Table[intXs[[$i]]->intFF[$i],{$i,Length[intXs]}]},{{Collect[#,_intFF]&/@(Join[#==0&/@StringyIdentity$X$All[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X$All]]],List@@OptionValue["Extra Equations"]]/.Dispatch[intXtoFF]),Reverse[intXtoFF[[All,2]]],"Parameters"->Xvars[n],"VarsPattern"->(Union[Cases[{#},_intFF,Infinity]]&)},Reverse/@intXtoFF}/.XctoVarName$FF]]


Options[StringyReduction$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Function"->intX$PTshift$sort};
Options[StringyRelations$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Function"->intX$PTshift$sort};
StringyReduction$X[n_,opts:OptionsPattern[]]:=Once[DeleteCases[RowReduce[Once[Reverse[Coefficient[#,intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]]]]&/@StringyIdentity$X$All[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X$All]]]]]//Simplify,{0..}]]
StringyRelations$X[n_,opts:OptionsPattern[]]:=Once[(coeff|->FirstCase[#,{1,_}][[2]]==-Plus@@Times@@@Cases[#,Except[{0,_}]][[2;;]]&@({coeff,Reverse[intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]]]}\[Transpose]))/@StringyReduction$X[n,opts]]


Options[StringyAscendRules$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
Options[StringyDescendRules$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Function"->intXshift$sort};
StringyAscendRules$X[n_,opts:OptionsPattern[]]:=Once[Table[RuleDelayed@@{#[[1]]/.XctoPatternIf[Xij,Negative],#[[2]]/.XctoVarName}&@SelectStringyEquations$AscendX[Equal@@Solve[#,int@@Xvars[n]][[1,1]]&/@
Select[#==0&/@StringyIdentity$X$All[n,opts],MemberQ[#,int@@Xvars[n],\[Infinity]]&],Xij][[1]],{Xij,Xvars[n]}]]
StringyDescendRules$X[n_,opts:OptionsPattern[]]:=Once[(RuleDelayed@@{#1[[1]]/.#2/.XctoPatternIf[#2[[1,1]],(m|->(#>m&))[#3]],#1[[2]]/.#2/.XctoVarName}&)@@@
(Append[#,Max[ExtractVariableFold[#[[1,2]],_int,#[[2,1,1]]+_,{_Integer,2}],0]]&@*(eq|->{eq,(#[[2]]->#[[2]]-#[[1]]&@*Sort/@List@@@Cases[eq[[1]],Subscript[X,__]+_])})/@
SelectStringyEquations$noshift[StringyRelations$X[n,PassOptions[opts,StringyDescendRules$X,StringyRelations$X]],PassOptions[opts,StringyDescendRules$X,SelectStringyEquations$noshift]])]


Options[StringyRandomReduction$X]={"Triangulation"->{},"cutoff"->{1,False},"F Polynomial"->StringyPolynomial,"Max Range"->10,"Precision"->10^-10};
StringyRandomReduction$X[n_,opts:OptionsPattern[]]:=With[{ranMax=OptionValue["Max Range"],dx=OptionValue["Precision"]},DeleteCases[Rationalize[RowReduce[Once[Reverse[Coefficient[#,intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]]]]&/@
StringyIdentity$X$All[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X$All]]]]/.Table[Xij->RandomReal[{-ranMax,ranMax}],{Xij,Xvars[n]}]],dx],{0..}]]


(************************ 5. Functions Part IV ***********************)


Options[FeynGraph$1Loop]={"Scaffolding"->False};
FeynGraph$1Loop[n_,OptionsPattern[Options[FeynGraph$1Loop]]]:=Once[Graph[Join[Table[Labeled[Subscript["V",i]\[UndirectedEdge]Subscript["V",Mod[i-1,n,1]],Subscript["y",i]],{i,n}],Table[Subscript["p",i]\[UndirectedEdge]Subscript["V",i],{i,n}]],VertexLabels->"Name"]]


Options[FeynGraph$1Loop]={"Scaffolding"->False};
FeynGraph$1Loop[n_Integer,OptionsPattern[Options[FeynGraph$1Loop]]]:=With[{circleLayout=({r,m,\[Theta],del}|->Delete[Table[{r Cos[2\[Pi] i/m+\[Theta]],-r Sin[2\[Pi] i/m+\[Theta]]},{i,0,m-1}],del])},If[OptionValue["Scaffolding"],
Once[Graph[Join[Table[Subscript["p",i],{i,2n}],Table[Subscript["p",2i-1,2i],{i,n}],Table[Subscript["V",i],{i,n}]],Join[Table[Labeled[Subscript["V",Mod[-1+i,n,1]]\[DirectedEdge]Subscript["V",i],Subscript[y,i]],{i,n}],Table[Labeled[Subscript["p",2 i-1]\[UndirectedEdge]Subscript["p",2i-1,2 i],Subscript[y,2 i-1,Mod[2 i,2 n,1]]],{i,n}],Table[Labeled[Subscript["p",2 i]\[UndirectedEdge]Subscript["p",2 i-1,2 i],Subscript[y,2 i,Mod[2 i+1,2 n,1]]],{i,n}],Table[Labeled[Subscript["p",2 i-1,2 i]\[UndirectedEdge]Subscript["V",i],Subscript[y,2 i-1,Mod[2 i+1,2 n,1]]],{i,n}]],VertexLabels->"Name",VertexCoordinates->Join[circleLayout[7/2,3n,-\[Pi]/(3n),List/@(3Range[n])],circleLayout[5/2,n,0,{}],circleLayout[1,n,0,{}]]]],
Once[Graph[Join[Table[Subscript["p",i],{i,n}],Table[Subscript["V",i],{i,n}]],Join[Table[Labeled[Subscript["V",Mod[i-1,n,1]]\[DirectedEdge]Subscript["V",i],Subscript[y,i]],{i,n}],Table[Labeled[Subscript["p",i]\[UndirectedEdge]Subscript["V",i],Subscript[y,i,Mod[i+1,n,1]]],{i,n}]],VertexLabels->"Name",VertexCoordinates->Join[circleLayout[5/2,n,0,{}],circleLayout[1,n,0,{}]]]]]]


Options[uPath]={"Scaffolding"->False,"Ordering"->"Clockwise"};
uPath[n_Integer,i_Integer,j_Integer,opts:OptionsPattern[]]:=Once[With[{thisVi=If[OptionValue["Scaffolding"],Ceiling[i/2],i],ReverseOrNot=If[OptionValue["Ordering"]==="Clockwise",{},{"Left"->"Right","Right"->"Left"}],ifcycle=(i==j||(i-j==1&&EvenQ[i]&&OptionValue["Scaffolding"])),graph=Once[ToExpression["List"<>StringTake[FullForm[FeynGraph$1Loop[n,Sequence@@FilterRules[{opts},Options[FeynGraph$1Loop]]]]//ToString,{6,-1}]]/.If[OptionValue["Ordering"]==="Clockwise",{},V1_\[DirectedEdge]V2_:>V2\[DirectedEdge]V1]]},
With[{edges=Once[List@@@graph[[3,1,2]]],pointPath=Once[If[!ifcycle,FindPath[Once[Graph@@graph],Subscript["p",i],Subscript["p",j],\[Infinity],All][[1]],If[FreeQ[#,{___,Subscript["V",a_],Subscript["V",b_],___}/;Mod[b-a-If[OptionValue["Ordering"]==="Clockwise",1,-1],n]==0],Reverse[#],#]&@Join[{Subscript["p",i],If[OptionValue["Scaffolding"],If[OddQ[i],Subscript["p",i,i+1],Subscript["p",i-1,i]],Nothing]},RotateLeft[#,Position[#,Subscript["V",thisVi]\[UndirectedEdge]_][[1,1]]-1]&@FindCycle[{Once[Graph@@(graph/.DirectedEdge->UndirectedEdge)],Subscript["V",thisVi]},\[Infinity],All][[1]]/.UndirectedEdge->Sequence,{If[OptionValue["Scaffolding"],If[OddQ[j],Subscript["p",j,j+1],Subscript["p",j-1,j]],Nothing],Subscript["p",j]}]//.{a___,b_,b_,c___}:>{a,b,c}]],
LeftOrRight=({#1,#2,Switch[#2,{Subscript["p",a_],Subscript["p",a_,b_],Subscript["V",_]},"Right",{Subscript["p",b_],Subscript["p",a_,b_],Subscript["V",_]},"Left",{Subscript["p",__],Subscript["V",_],Subscript["V",_]},"Left"/.ReverseOrNot,{Subscript["V",_],Subscript["V",_],Subscript["V",_]},"Right"/.ReverseOrNot,{Subscript["V",_],Subscript["V",_],Subscript["p",__]},"Left"/.ReverseOrNot,{Subscript["V",_],Subscript["p",a_,b_],Subscript["p",a_]},"Left",{Subscript["V",_],Subscript["p",a_,b_],Subscript["p",b_]},"Right",{Subscript["p",a_],Subscript["p",a_,b_],Subscript["p",b_]},"Left",{Subscript["p",b_],Subscript["p",a_,b_],Subscript["p",a_]},"Right",_,"Fixed"]}&)},
Table[LeftOrRight@@{Cases[Once[Union[edges,{Reverse[#[[1]]],#[[2]]}&/@Cases[edges,{_UndirectedEdge,_}]]],{_[pointPath[[$i]],pointPath[[$i+1]]],_}][[1,2]],If[$i<Length[pointPath]-1,{pointPath[[$i]],pointPath[[$i+1]],pointPath[[$i+2]]},{}]},{$i,Length[pointPath]-1}]]]]
uPath[n_Integer,SuperPlus[i_]|SuperMinus[j_],opts:OptionsPattern[]]:=With[{thisVi=If[OptionValue["Scaffolding"],Ceiling[(i+j)/2],i+j],upath=uPath[n,i,i,j,j,"Scaffolding"->OptionValue["Scaffolding"],"Ordering"->If[TrueQ[And[j]],"Clockwise","CounterClockwise"]],break=If[OptionValue["Scaffolding"],-3,-2]},Join[upath[[;;break-1]],{upath[[break]]/.{"Left"->"Right","Right"->"Left",Subscript["p",a_]:>Subscript["V",Mod[a+Sign[j/i],n,1]],Subscript["p",a_,b_]:>Subscript["V",Mod[b/2+Sign[j/i],n,1]]},{Subscript[y,Mod[thisVi+UnitStep[j/i],n,1]],{},"Fixed"}}]]


Options[uPolynomial]={"Scaffolding"->False};
uPolynomial[n_Integer,ij__Integer|k_SuperPlus|k_SuperMinus,opts:OptionsPattern[]]:=Once[#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&@(Dot@@(uPath[n,ij,k,opts]/.{{y_,_,"Left"}:>{{y,y},{0,1}},{y_,_,"Right"}:>{{y,0},{1,1}},{__,"Fixed"}->Nothing}/.{Subscript[y,a_,b_]/;Mod[b-a-1,If[OptionValue["Scaffolding"],2n,n]]==0->1}))]
uPolynomial[n_Integer,Subscript[i_,\[Infinity]]|Subscript[j_,-\[Infinity]],opts:OptionsPattern[]]:=Once[With[{uMatrices={Dot@@#1[[;;#2-1]],Dot@@#1[[#2;;]]}&@@{uPath[n,If[TrueQ[And[j]],SuperPlus[i],SuperMinus[j]],opts][[;;-2]]/.{{y_,_,"Left"}:>{{y,y},{0,1}},{y_,_,"Right"}:>{{y,0},{1,1}}}/.{Subscript[y,a_,b_]/;Mod[b-a-1,If[OptionValue["Scaffolding"],2n,n]]==0->1},If[OptionValue["Scaffolding"],3,2]}},
With[{diag2=Diagonal[uMatrices[[2]]],nondiag2=uMatrices[[2]]-DiagonalMatrix[Diagonal[uMatrices[[2]]]]},Module[{m},Simplify[Together[#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&@(uMatrices[[1]] . (DiagonalMatrix[diag2^m]+(diag2[[2]]^m-diag2[[1]]^m)nondiag2/(diag2[[2]]-diag2[[1]])))]//.{Times[a_^m,b__]+c_/;FreeQ[c,m]:>c,a_^m+c_/;FreeQ[c,m]:>c}]]]]]


Options[StringyIntegrand$XY]={"Scaffolding"->False,"Surfacehedron"->"Dn\[Infinity]"};
StringyIntegrand$XY[n_Integer,opts:OptionsPattern[]]:=Once[With[{m=If[OptionValue["Scaffolding"],2n,n]},PowerExpand[Product[If[#===0,1,#]&@uPolynomial[n,i,j,Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[X,i,j],{i,m},{j,m}]*
If[StringContainsQ[OptionValue["Surfacehedron"],"inf"|"\[Infinity]",IgnoreCase->True],Product[uPolynomial[n,Subscript[i,-\[Infinity]],Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[OverTilde[Y],i],{i,m}],Product[uPolynomial[n,SuperPlus[i],Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[Y,i],{i,m}]Product[uPolynomial[n,SuperMinus[i],Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[OverTilde[Y],i],{i,m}]]/.a_Plus:>Factor[a]]]]


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
