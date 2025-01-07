(* ::Package:: *)

(************************ 0. Info and copyright ***********************)


StringyIBP$Version={"0.0.7","2024.8.2"};


(* Introduction to StringyIBP *)

(* To be completed...
*)


(* Update notes *)

(* 0.0.1    2023.6.7      Add Part I~III of this package.
   0.0.2    2023.6.27     Add Part IV for loop integrand.
   0.0.3    2023.8.30     Change default triangulation.
   0.0.4    2024.1.10     1.Add interface for FiniteFlow.
                          2.Use Options to specify certain parameters.
   0.0.5    2024.4.25     1.Add scaffolding.
                          2.Use Dn\[Infinity] instead of Dn.
   0.0.6    2024.5.7      1.Add Parke-Taylor form.
                          2.Add interface for syzygy.
                          3.Rewrite Options passing.
   0.0.7    2024.8.2      1.Add several functions about curves.
                          2.Adjust notation to be consistent with arXiv:2309.15913.
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


MultiChoiceToSequence[multichoice_List]:=With[{poslist=Position[multichoice,_List,{1}]},If[poslist==={},{multichoice},Fold[Flatten[Table[ReplacePart[multiseq,#2->elem],{multiseq,#1},{elem,multiseq[[#2]]}],1]&,{multichoice},poslist[[All,1]]]]]


DistributePolePosition[level_,rank_]:=Block[{a},If[level===0,{ConstantArray[0,rank]},(Exponent[(List@@Expand[(Plus@@Array[a,rank])^level]),#]&/@Array[a,rank])//Transpose]]


Options[ParallelExpand]={"PieceLength"->500,Method->"CoarsestGrained"};
ParallelExpand[expr_Plus,OptionsPattern[]]:=With[{piecelength=OptionValue["PieceLength"]},Module[{progress=0},SetSharedVariable[progress];
Monitor[Plus@@ParallelTable[(progress++;Expand[expr[[piecelength i+1;;Min[piecelength(i+1),expr//Length]]]]),{i,0,Ceiling[Length[expr]/piecelength]-1},Method->OptionValue[Method]],
ToString[progress]<>"/"<>ToString[Ceiling[Length[expr]/piecelength]]<>" terms have been expanded."]]]


Options[ParallelReplace]={"PieceLength"->500,Method->"CoarsestGrained"};
ParallelReplace[expr:_List|_Integer,rules_,levelspec:_?LevelSpecQ:All,OptionsPattern[]]:=With[{piecelength=OptionValue["PieceLength"]},Module[{progress=0,output},SetSharedVariable[progress];
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


Options[yRenameRules]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
yRenameRules[n_,OptionsPattern[]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]]},Switch[Association[OptionValue["Notation"]]["y"],
"Sequence",<|"Tree"->Table[Subscript[y,Sequence@@Xi[[$i,2;;]]]->Subscript[y,$i],{$i,Length[Xi]}],"1-Loop Scaffolding"->{Subscript[y,i_]:>Subscript[y,(i+1)/2],Subscript[Y,i_]:>Subscript[Y,(i+1)/2],Subscript[OverTilde[Y],i_]:>Subscript[OverTilde[Y],(i+1)/2]}|>,
"Curve",<|"Tree"->Table[Subscript[y,$i]->Subscript[y,Sequence@@Xi[[$i,2;;]]],{$i,Length[Xi]}],"1-Loop Scaffolding"->{Subscript[y,i_]:>Subscript[y,2i-1],Subscript[Y,i_]:>Subscript[Y,2i-1],Subscript[OverTilde[Y],i_]:>Subscript[OverTilde[Y],2i-1]}|>]]]


Options[ytouRules]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
ytouRules[n_,opts:OptionsPattern[]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],del$c=$GlobalConventions$DeletedCij$},
Module[{xvar=Complement[Xvars[n],Xi],cvar=Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]],sol,ytou},
sol=Solve[(cvar/.Subscript[c,i_,j_]:>Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n])==0,xvar][[1]]/.X->u;
ytou=With[{ui=(Xi/.X->u)},Table[Subscript[y,i]->ui[[i]]Product[sol[[j,1]]^Coefficient[sol[[j,2]],ui[[i]]],{j,1,Length@sol}],{i,1,Length@ui}]/.yRenameRules[n,opts]["Tree"]]]]]


Options[utoyRules]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
utoyRules[n_,opts:OptionsPattern[]]:=Once[Module[{ytou=ytouRules[n,opts]/.Rule->Equal,ueqs},
ueqs=Table[uij/.Subscript[u,i_,j_]:>(1-Subscript[u,i,j]==Product[Subscript[u,k,l],{k,i+1,j-1},{l,Range[i-1]~Join~Range[j+1,n]}])/.{Subscript[u,i_,j_]/;Abs[j-i]<=1->1}/.Subscript[u,i_,j_]/;i>j:>Subscript[u,j,i],{uij,Xvars[n,"X"->u]}];
Solve[ytou~Join~ueqs,Xvars[n,"X"->u]][[1]]/.yRenameRules[n,opts]["Tree"]]]


Options[ytozRules]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
ytozRules[n_,opts:OptionsPattern[]]:=Once[With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],del$c=$GlobalConventions$DeletedCij$},Module[{xvar=Complement[Xvars[n],Xi],
cvar=Complement[Xvars[n,"X"->c],Xi/.Subscript[X,i_,j_]:>Subscript[c,Mod[i+del$c,n,1],Mod[j+del$c,n,1]]/.Subscript[c,i_,j_]/;i>j:>Subscript[c,j,i]],sol,ytou,ueqs},
sol=Solve[(cvar/.Subscript[c,i_,j_]:>Subscript[X,i,j]+Subscript[X,i+1,j+1]-Subscript[X,i,j+1]-Subscript[X,i+1,j]//.Xcal[n])==0,xvar][[1]]/.X->u;
ytou=With[{ui=(Xi/.X->u)},Table[Subscript[y,i]->ui[[i]]Product[sol[[j,1]]^Coefficient[sol[[j,2]],ui[[i]]],{j,1,Length@sol}],{i,1,Length@ui}]];
Cancel[ytou/.Subscript[u,i_,j_]:>(Subscript[z,i-1]-Subscript[z,j])(Subscript[z,i]-Subscript[z,j-1])/((Subscript[z,i]-Subscript[z,j])(Subscript[z,i-1]-Subscript[z,j-1]))/.Subscript[z,i_]:>Subscript[z,Mod[i,n,1]]]/.yRenameRules[n,opts]["Tree"]]]]


Options[ztoyRules]={"Triangulation"->{},"Fix SL2"->"1,n-1,n","Notation"->{"y"->"Curve"}};
ztoyRules[n_,opts:OptionsPattern[]]:=With[{fixSL2=SortBy[Switch[OptionValue["Fix SL2"],"1,n-1,n",{Subscript[z,1]->0,Subscript[z,n-1]->1,Subscript[z,n]->\[Infinity]},"1,2,n",{Subscript[z,1]->0,Subscript[z,2]->1,Subscript[z,n]->\[Infinity]},_,OptionValue["Fix SL2"]],Count[#,\[Infinity],\[Infinity]]&]},
SortBy[Join[fixSL2,Solve[Map[Limit[#,fixSL2[[-1]]]&,ytozRules[n,Sequence@@FilterRules[{opts},Options[ytozRules]]]/.Rule->Equal/.fixSL2[[;;-2]],{2}],Complement[Table[Subscript[z,$i],{$i,n}],fixSL2[[;;,1]]]][[1]]//Factor],Count[#,\[Infinity],\[Infinity]]&]/.yRenameRules[n,Sequence@@FilterRules[{opts},Options[ytozRules]]]["Tree"]]


Options[StringyIntegrand$X]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
Options[StringyIntegrand$Xc]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
Options[StringyPolynomial]={"Triangulation"->{},"Notation"->{"y"->"Curve"}};
StringyIntegrand$X[n_,opts:OptionsPattern[]]:=PowerExpand[Product[Subscript[u,i,j]^Subscript[X,i,j],{i,n-2},{j,i+2,If[i==1,n-1,n]}]/Product[Subscript[y,i],{i,n-3}]/.utoyRules[n,opts]/.yRenameRules[n,opts]["Tree"]]
StringyIntegrand$Xc[n_,opts:OptionsPattern[]]:=PowerExpand[Product[Subscript[u,i,j]^Subscript[X,i,j],{i,n-2},{j,i+2,If[i==1,n-1,n]}]/Product[Subscript[y,i],{i,n-3}]/.utoyRules[n,opts]/.yRenameRules[n,opts]["Tree"]/.Xtoc[n,Sequence@@FilterRules[{opts},Options[Xtoc]]]]
StringyPolynomial[n_,i_,j_,opts:OptionsPattern[]]:=Once[Times@@Cases[StringyIntegrand$Xc[n,opts],_^-Subscript[c,i,j]][[;;,1]]]


Options[intPT$Xc]={"Triangulation"->{},"Fix SL2"->"1,n-1,n"};
Options[intPT$X]={"Triangulation"->{},"Fix SL2"->"1,n-1,n"};
intPT$Xc[perm__Integer,opts:OptionsPattern[]]:=With[{PT=(Times@@({i,j}|->1/(Subscript[z,i]-Subscript[z,j]))@@@({{##},RotateLeft@{##}}\[Transpose])&),ztoy=ztoyRules[Length[{perm}],opts],n=Length[{perm}]},
With[{prefactor=Limit[PT[perm]/PT@@Range[n]/.ztoy[[;;-2]],ztoy[[-1]]]//Factor,shiftRules=SortBy[Rule@@@(List@@StringyIntegrand$Xc[n,Sequence@@FilterRules[{opts},Options[StringyIntegrand$Xc]]]/.Power->List/.{y_,Xc_Subscript+n_Integer}:>{y,Xc}/.{y_,-Xc_Subscript}:>{y,Xc^-1}),-LeafCount[#[[1]]]&],intXc=int@@Xcvars[n,Sequence@@FilterRules[{opts},Options[Xcvars]]]},
If[NumericQ[prefactor],prefactor intXc,If[Head[prefactor]===Times,Select[prefactor,FreeQ[#,Subscript[y,__]]&]intXc/.(Select[List@@prefactor,!FreeQ[#,Subscript[y,__]]&]/.shiftRules/.{Xc_Subscript:>(Xc->Xc+1),Xc_Subscript^n_:>(Xc->Xc+n)}),Print["Error."]]]]]
intPT$X[perm__Integer,opts:OptionsPattern[]]:=int$XctoX[intPT$Xc[perm,opts],Sequence@@FilterRules[{opts},Options[int$XctoX]]]
intX$PTshift$sort[inteq_]:=With[{n=(3+Sqrt[9+8 Length[Cases[{inteq},_int,\[Infinity]][[1]]]])/2},With[{intPTs=Once[Alternatives@@Union@Cases[intPT$X[1,Sequence@@#,n-1,n]&/@Permutations[Range[2,n-2]],_int,\[Infinity]]]},{Count[{inteq},Except[intPTs,_int],\[Infinity]],intXshift$sort[inteq]}]]


(************************ 4. Functions Part III ***********************)


Options[TrivialIdentity$Xc]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
Options[TrivialIdentity$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
TrivialIdentity$Xc[n_,i_,j_,OptionsPattern[]]:=With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],p=(OptionValue["F Polynomial"][##,"Notation"->{"y"->"Sequence"}]&)},
With[{getRules=(expr|->Array[Xi[[#]]->Xi[[#]]+Exponent[expr,Subscript[y,#]]&,n-3]),intXc=int@@Xcvars[n,"Triangulation"->Xi],toList=(Switch[#,_Plus,List@@#,0,{},_,{#}]&),Xtri=("Triangulation"->Xi)},
If[p[n,i,j,Xtri]=!=1,intXc-Plus@@((intXc/.getRules[#]&)/@(toList@Expand@p[n,i,j,Xtri])/.Subscript[c,i,j]->Subscript[c,i,j]+1),0]]]
TrivialIdentity$X[n_,i_,j_,opts:OptionsPattern[]]:=int$XctoX[TrivialIdentity$Xc[n,i,j,opts],Sequence@@FilterRules[{opts},Options[int$XctoX]]]


Options[IBP$Identity$Xc]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
Options[IBP$Identity$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
IBP$Identity$Xc[n_,k_,opts:OptionsPattern[]]:=With[{Xi=Init[OptionValue["Triangulation"],Xtri$Default[n]],p=(OptionValue["F Polynomial"][##,"Notation"->{"y"->"Sequence"}]&)},
With[{getRules=(expr|->Array[Xi[[#]]->Xi[[#]]+Exponent[expr,Subscript[y,#]]&,n-3]),intXc=int@@Xcvars[n,"Triangulation"->Xi],toList=(Switch[#,_Plus,List@@#,0,{},_,{#}]&),Xtri="Triangulation"->Xi},
If[1<=k<=n-3,Xi[[k]]intXc-Sum[Subscript[c,i,j]Plus@@((intXc/.getRules[#]&)/@(toList@Expand@D[p[n,i,j,Xtri],Subscript[y,k]])/.{Xi[[k]]->Xi[[k]]+1,Subscript[c,i,j]->Subscript[c,i,j]+1}),{i,1,n},{j,i,n}],Print["1\[LessEqual]k\[LessEqual]n-3?"]]//Expand]]
IBP$Identity$X[n_,k_,opts:OptionsPattern[]]:=int$XctoX[IBP$Identity$Xc[n,k,opts],Sequence@@FilterRules[{opts},Options[int$XctoX]]]/.ctoX[n]


Options[CheckStringyIdentity]={"Triangulation"->{}};
CheckStringyIdentity[id_,opts:OptionsPattern[]]:=With[{n=(3+Sqrt[9+8 Length[Cases[id,_int,\[Infinity]][[1]]]])/2,IBPtag=Cases[id//Simplify,_int*Subscript[X,__],\[Infinity]][[All,-1]],yij=(Subscript[y,Sequence@@#[[2;;]]]&)},
With[{integrandX=StringyIntegrand$X[n,"Notation"->{"y"->"Curve"},opts],integrandXc=StringyIntegrand$Xc[n,"Notation"->{"y"->"Curve"},opts]},
With[{intXRule=RuleDelayed@@{int@@Xvars[n]/.XctoPattern,integrandX/.XctoVarName},intXcRule=RuleDelayed@@{int@@Xcvars[n,opts]/.XctoPattern,integrandXc/.XctoVarName}},
If[MemberQ[id,int[___,Subscript[c,__]],\[Infinity]],(id/.intXcRule)-If[IBPtag=!={},D[yij@IBPtag[[1]] integrandXc,yij@IBPtag[[1]]],0],(id/.intXRule)-If[IBPtag=!={},D[yij@IBPtag[[1]] integrandX,yij@IBPtag[[1]]],0]]==0//Simplify]]]


Options[StringyIdentity$X]={"Triangulation"->{},"Collect int"->False,"F Polynomial"->StringyPolynomial};
Options[StringyIdentity$Xc]={"Triangulation"->{},"Collect int"->False,"F Polynomial"->StringyPolynomial};
Options[StringyIdentity$X$cyclic]={"Triangulation"->{},"Collect int"->False,"F Polynomial"->StringyPolynomial};
Options[StringyIdentity$X$shift]={"Triangulation"->{},"Collect int"->False,"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
Options[StringyIdentity$X$All]={"Triangulation"->{},"Collect int"->False,"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
StringyIdentity$X[n_,opts:OptionsPattern[]]:=Once[With[{simplify=If[TrueQ@OptionValue["Collect int"],Collect[#,_int,Factor]&,Expand]},DeleteCases[Flatten[Table[simplify@TrivialIdentity$X[n,i,j,Sequence@@FilterRules[{opts},Options[TrivialIdentity$X]]]==0,{i,1,n},{j,i,n}]]~Join~Flatten[Table[simplify@IBP$Identity$X[n,k,Sequence@@FilterRules[{opts},Options[IBP$Identity$X]]]==0,{k,n-3}]],True]]]
StringyIdentity$Xc[n_,opts:OptionsPattern[]]:=Once[With[{simplify=If[TrueQ@OptionValue["Collect int"],Collect[#,_int,Factor]&,Expand]},DeleteCases[Flatten[Table[simplify@TrivialIdentity$Xc[n,i,j,Sequence@@FilterRules[{opts},Options[TrivialIdentity$Xc]]]==0,{i,1,n},{j,i,n}]]~Join~Flatten[Table[simplify@IBP$Identity$Xc[n,k,Sequence@@FilterRules[{opts},Options[IBP$Identity$Xc]]]==0,{k,n-3}]],True]]]
StringyIdentity$X$cyclic[n_,opts:OptionsPattern[]]:=Once[DeleteDuplicates[Table[Xc$cyclicPerm[(#[[1]]-#[[2]])&/@Once[StringyIdentity$X[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X]]]],n,m],{m,0,n-1}]//Flatten]]
StringyIdentity$X$shift[n_,opts:OptionsPattern[]]:=Once[With[{k=OptionValue["cutoff"][[1]]},(#[[1]]-#[[2]])&/@FullSimplify[DeleteDuplicates[Select[Flatten@
Table[eq/.Apply[Rule,{Xvars[n],Xvars[n]+#}\[Transpose]&/@Tuples[Range[0,k],n (n-3)/2],{2}],{eq,StringyIdentity$X[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X]]]}],intXshift$cutoff[#,Sequence@@FilterRules[{opts},Options[intXshift$cutoff]]]&]]]]]
StringyIdentity$X$All[n_,opts:OptionsPattern[]]:=Once[DeleteDuplicates[Table[Xc$cyclicPerm[Once[StringyIdentity$X$shift[n,opts]],n,m],{m,0,n-1}]//Flatten]]


Options[intXs$List]={"cutoff"->{1,True},"Sort Function"->intX$PTshift$sort};
intXs$List[n_,opts:OptionsPattern[]]:=Once[With[{k=OptionValue["cutoff"][[1]]},SortBy[Select[int@@@(Xvars[n]+#&/@Tuples[Range[0,k+1],n (n-3)/2]),intXshift$cutoff[#,Sequence@@FilterRules[{opts},Options[intXshift$cutoff]]]&],OptionValue["Sort Function"]]]]


Options[StringyReductionDataFF$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Extra Equations"->{},"Sort Function"->intX$PTshift$sort,"intFF"->intFF};
StringyReductionDataFF$X[n_,opts:OptionsPattern[]]:=With[{intXs=intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]],XctoVarName$FF=Dispatch[#->(#/.XctoVarName)&/@Xvars[n]],intFF=OptionValue["intFF"]},
With[{intXtoFF=Table[intXs[[$i]]->intFF[$i],{$i,Length[intXs]}]},{{Collect[#,_intFF]&/@(Join[#==0&/@StringyIdentity$X$All[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X$All]]],List@@OptionValue["Extra Equations"]]/.Dispatch[intXtoFF]),Reverse[intXtoFF[[All,2]]],"Parameters"->Xvars[n],"VarsPattern"->(Union[Cases[{#},_intFF,Infinity]]&)},Reverse/@intXtoFF}/.XctoVarName$FF]]


Options[StringyReductionDataSyzygy$X]={"Triangulation"->{},"F Polynomial"->StringyPolynomial};
StringyReductionDataSyzygy$X[n_,opts:OptionsPattern[]]:=With[{rules=Flatten@Table[StringJoin[sym,ToString/@List@@Xvars[n][[$i,2;;]]]->sym<>ToString[$i],{sym,{"n","z"}},{$i,n (n-3)/2}]},Module[{zeros,zz,nn},zeros=StringyIdentity$X$cyclic[n,opts]//.int[a___,Subscript[X,i_,j_]+k_,b___]:>(zz[i,j]^k) . int[a,Subscript[X,i,j],b]//.Times[Subscript[X,i_,j_],expr:_int|_Dot]:>expr . nn[i,j];If[Union@Cases[zeros,_int,\[Infinity]]==={int@@Xvars[n]},
{StringReplace[ToString[SortBy[zeros/._int->1/.Dot[a___,1,b___]:>Dot[a,b]//.{Dot[a___,zz[i1_,j1_],nn[i2_,j2_],b___]/;{i1,j1}=!={i2,j2}:>Dot[a,nn[i2,j2],zz[i1,j1],b],Dot[a___,zz[i_,j_],nn[i_,j_],b___]:>Dot[a,nn[i,j],zz[i,j],b]+Dot[a,zz[i,j],b]},LeafCount]/.{zz[i_,j_]:>ToExpression["z"<>ToString[i]<>ToString[j]],nn[i_,j_]:>ToExpression["n"<>ToString[i]<>ToString[j]]}],Append[rules,"."->"*"]],Reverse/@rules},Print["Error."]]]]


Options[StringyReduction$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Function"->intX$PTshift$sort};
Options[StringyRelations$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Function"->intX$PTshift$sort};
StringyReduction$X[n_,opts:OptionsPattern[]]:=Once[DeleteCases[RowReduce[Once[Reverse[Coefficient[#,intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]]]]&/@StringyIdentity$X$All[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X$All]]]]]//Simplify,{0..}]]
StringyRelations$X[n_,opts:OptionsPattern[]]:=Once[(coeff|->FirstCase[#,{1,_}][[2]]==-Plus@@Times@@@Cases[#,Except[{0,_}]][[2;;]]&@({coeff,Reverse[intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]]]}\[Transpose]))/@StringyReduction$X[n,opts]]


Options[StringyAscendRules$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial};
Options[StringyDescendRules$X]={"Triangulation"->{},"cutoff"->{1,True},"F Polynomial"->StringyPolynomial,"Sort Function"->intXshift$sort};
StringyAscendRules$X[n_,opts:OptionsPattern[]]:=Once[Table[RuleDelayed@@{#[[1]]/.XctoPatternIf[Xij,Negative],Collect[#[[2]]/.XctoVarName,_int]}&@SelectStringyEquations$AscendX[Equal@@Solve[#,int@@Xvars[n]][[1,1]]&/@
Select[#==0&/@StringyIdentity$X$cyclic[n,opts],MemberQ[#,int@@Xvars[n],\[Infinity]]&],Xij][[1]],{Xij,Xvars[n]}]]
StringyDescendRules$X[n_,opts:OptionsPattern[]]:=Once[(RuleDelayed@@{#1[[1]]/.#2/.XctoPatternIf[#2[[1,1]],(m|->(#>m&))[#3]],#1[[2]]/.#2/.XctoVarName}&)@@@
(Append[#,Max[ExtractVariableFold[#[[1,2]],_int,#[[2,1,1]]+_,{_Integer,2}],0]]&@*(eq|->{eq,(#[[2]]->#[[2]]-#[[1]]&@*Sort/@List@@@Cases[eq[[1]],Subscript[X,__]+_])})/@
SelectStringyEquations$noshift[StringyRelations$X[n,PassOptions[opts,StringyDescendRules$X,StringyRelations$X]],Sequence@@FilterRules[{opts},Options[SelectStringyEquations$noshift]]])]


Options[StringyRandomReduction$X]={"Triangulation"->{},"cutoff"->{1,False},"F Polynomial"->StringyPolynomial,"Max Range"->10,"Precision"->10^-10};
StringyRandomReduction$X[n_,opts:OptionsPattern[]]:=With[{ranMax=OptionValue["Max Range"],dx=OptionValue["Precision"]},DeleteCases[Rationalize[RowReduce[Once[Reverse[Coefficient[#,intXs$List[n,Sequence@@FilterRules[{opts},Options[intXs$List]]]]]&/@
StringyIdentity$X$All[n,Sequence@@FilterRules[{opts},Options[StringyIdentity$X$All]]]]/.Table[Xij->RandomReal[{-ranMax,ranMax}],{Xij,Xvars[n]}]],dx],{0..}]]


(************************ 5. Functions Part IV ***********************)


Options[DotSimplify]={"Dot"->{Dot,CenterDot}};
DotSimplify[expr_,OptionsPattern[]]:=With[{dots=Alternatives@@OptionValue["Dot"]},expr//.{(dot:dots)[a___,b_^m1_.,b_^m2_.,c___]:>dot[a,b^m1 b^m2,c],(dot:dots)[a___,1,b___]:>dot[a,b],(dot:dots)[a___,k_?NumberQ b_,c___]:>k dot[a,b,c]}]


(* ResourceFunction["SignedVectorAngle"] from https://resources.wolframcloud.com/FunctionRepository/resources/SignedVectorAngle *)
(*SignedVectorAngle[v1_List,v2_List]/;Length[v1]===2&&Length[v2]===2:=If[VectorAngle[v1,v2]===Pi,Pi,Sign[Last[Cross[Append[v1,0],Append[v2,0]]]]VectorAngle[v1,v2]]*)
SignedVectorAngle[vec1_List,vec2_List]:=With[{v1=N[vec1],v2=N[vec2]},If[VectorAngle[v1,v2]===Pi,Pi,Sign[Last[Cross[Append[v1,0],Append[v2,0]]]]VectorAngle[v1,v2]]]/;Length[vec1]===2&&Length[vec2]===2


FindAllPathsInEdges[graph_Graph,v1_,v2_]:=If[v1===v2,{{}},With[{edges=Join[EdgeList[graph],Cases[EdgeList[graph],_UndirectedEdge]/.$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i]},
With[{VertToEdge=(Cases[edges,_[#1,#2]]&)},Flatten[MultiChoiceToSequence/@Table[VertToEdge[path[[$i]],path[[$i+1]]],{path,FindPath[graph,v1,v2,\[Infinity],All]},{$i,Length[path]-1}],1]]]]


MergeMarkedSequence[seq1_List,seq2_List]:=FixedPoint[With[{this1=#[[1]],this2=#[[2]],done=#[[3]]},If[Flatten[this1]=!=Flatten[this2],Print["MergeMarkedSequences Error: ",#];Return[]];If[this1===this2,{{},{},Join[done,this1]},Switch[{this1[[1]],this2[[1]]},{a_,a_},{this1[[2;;]],this2[[2;;]],Append[done,this1[[1]]]},
{_List,Except[_List]},With[{pos=Position[this2,_List,{1}]},Switch[pos,{},{{},{},Join[done,this1]},{{a_},b___}/;a>Length[this1[[1]]],{this1[[2;;]],this2[[Length[this1[[1]]]+1;;]],Append[done,this1[[1]]]},{{a_},b___}/;a<=Length[this1[[1]]],If[pos[[1,1]]+Length[this2[[pos[[1,1]]]]]-1<=Length[this1[[1]]],{this1,FlattenAt[this2,pos[[1,1]]],done},{Join[this1[[1]],this1[[2;;]]],Prepend[this2[[pos[[1,1]]+1;;]],Join[this1[[1,;;pos[[1,1]]-1]],this2[[pos[[1,1]]]]]],done}]]],
{Except[_List],_List},With[{pos=Position[this1,_List,{1}]},Switch[pos,{},{{},{},Join[done,this2]},{{a_},b___}/;a>Length[this2[[1]]],{this1[[Length[this2[[1]]]+1;;]],this2[[2;;]],Append[done,this2[[1]]]},{{a_},b___}/;a<=Length[this2[[1]]],If[pos[[1,1]]+Length[this1[[pos[[1,1]]]]]-1<=Length[this2[[1]]],{FlattenAt[this1,pos[[1,1]]],this2,done},{Prepend[this1[[pos[[1,1]]+1;;]],Join[this2[[1,;;pos[[1,1]]-1]],this1[[pos[[1,1]]]]]],Join[this2[[1]],this2[[2;;]]],done}]]],
{a_List,b_List},If[Length[this1[[1]]]>Length[this2[[1]]],{this1,FlattenAt[this2,1],done},{FlattenAt[this1,1],this2,done}]]]]&,{seq1,seq2,{}},Length[Flatten[seq1]]+1][[-1]]


(*MarkCommonSubsequence[path_List,cycle_List]:=With[{MendMarkedSequence=(markedseq|->With[{overlaps=SortBy[Cases[markedseq,_List],-Length[#]&]},SequenceReplace[markedseq,Thread[overlaps->overlaps]]])},
Fold[MergeMarkedSequence,Table[MendMarkedSequence@Replace[SequenceAlignment[path,RotateLeft[cycle,$i],GapPenalty->-1],{a_List,b_List}:>Sequence@@a,{1}],{$i,0,Length[cycle]-1}]]]*)


MarkCommonSubsequence[path_List,cycle_List]:=With[{RotateToBeginning=(RotateLeft[#1,FirstPosition[#1,#2][[1]]-1]&),RepeatThisCycle=(Flatten@Join[Table[#1,Floor[#2/Length[#1]]],#1[[;;Mod[#2,Length[#1]]]]]&),FirstDifferencePosition=(FirstPosition[Inner[SameQ,#1,#2,List],False,{Length[#1]+1},{1}][[1]]&)},
FixedPoint[markedseq|->With[{pos=FirstPosition[markedseq,Alternatives@@cycle,{0},{1}][[1]]},If[pos==0,markedseq,With[{common$length=FirstDifferencePosition[markedseq[[pos;;]],RepeatThisCycle[RotateToBeginning[cycle,markedseq[[pos]]],Length[markedseq]-pos+1]]-1},
Join[markedseq[[;;pos-1]],{markedseq[[pos;;pos+common$length-1]]},markedseq[[pos+common$length;;]]]]]],path,Count[path,Alternatives@@cycle]]]


Options[FindCycleBridge]={"2-cycle"->{}};
FindCycleBridge[graph_Graph,cycle_List,v1_,v2_,loop_Integer:1,opts:OptionsPattern[]]:=Once[With[{cycles$len2=OptionValue["2-cycle"]},
Union[Flatten[Table[Join[path1,Sequence@@Table[RotateLeft[cycle,$i-1],loop],path2]//.{a___,e_[b_,c_],e_[c_,b_],d___}/;FreeQ[cycles$len2,e[b,c]]:>{a,d},{$i,Length[cycle]},{path1,FindAllPathsInEdges[graph,v1,cycle[[$i,1]]]},{path2,FindAllPathsInEdges[graph,cycle[[$i,1]],v2]}],2]]]]


(*InsertCycleToPath[path_List,cycle_List,loop_Integer:1]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&)},If[!AllTrue[Tally[Level[cycle,{2}]],#[[2]]==2&],Print["Not fundamental cycle."];Return[]];If[DisjointQ[Level[path,{2}],Level[cycle,{2}]],Print["Disjoint path and cycle."];Return[]];If[DisjointQ[path,ReverseThisPath@cycle],
With[{intersections=Intersection[Level[path,{2}],Level[cycle,{2}]],ToInsert=Table[RotateLeft[cycle,FirstPosition[cycle,#1\[UndirectedEdge]_|#1\[DirectedEdge]_][[1]]-1],#2]&},Union@Flatten[Table[Flatten@Insert[path,ToInsert[inter,loop],pos],{inter,intersections},{pos,Union[Plus@@@Position[path,inter]-1]}],1]],
With[{overlaps=MarkCommonSubsequence[path,ReverseThisPath@cycle],ToInsert=With[{cycle$r=RotateLeft[cycle,FirstPosition[cycle,ReverseThisPath[#1][[1]]][[1]]-1]},Join[cycle$r[[Length[#1]+1;;]],Sequence@@Table[cycle$r,#2-1]]]&},
Union@Flatten[Table[If[Length[overlaps[[pos]]]<=Length[cycle],{Flatten@ReplacePart[overlaps,pos->ToInsert[overlaps[[pos]],loop]]},Table[Flatten@Join[overlaps[[;;pos-1]],overlaps[[pos,;;$i-1]],ToInsert[overlaps[[pos,$i;;Length[cycle]+$i-1]],loop],overlaps[[pos,Length[cycle]+$i;;]],overlaps[[pos+1;;]]],{$i,Length[overlaps[[pos]]]-Length[cycle]+1}]],{pos,Position[overlaps,_List,{1}][[All,1]]}],1]]]]/;loop>0*)


Options[InsertCycleToPath]={"2-cycle"->{}};
InsertCycleToPath[path_List,cycle_List,loop_Integer:1,opts:OptionsPattern[]]:=With[{intersections=Intersection[Level[path,{2}],Level[cycle,{2}]],ToInsert=(Table[RotateLeft[cycle,FirstPosition[cycle,#1\[UndirectedEdge]_|#1\[DirectedEdge]_][[1]]-1],#2]&),cycles$len2=OptionValue["2-cycle"]},If[!AllTrue[Tally[Level[cycle,{2}]],#[[2]]==2&],Print["Not simple cycle."];Return[]];If[intersections==={},Print["Disjoint path and cycle."];Return[]];
Union[Flatten[Table[Flatten@Insert[path,ToInsert[inter,loop],pos]//.{a___,e_[b_,c_],e_[c_,b_],d___}/;FreeQ[cycles$len2,e[b,c]]:>{a,d},{inter,intersections},{pos,Union[Plus@@@Position[path,inter]-1]}],1]]]/;loop>0
InsertCycleToPath[path_List,cycle_List,loop_Integer,opts:OptionsPattern[]]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&)},If[loop==0,{path},InsertCycleToPath[path,ReverseThisPath@cycle,-loop,opts]]]/;loop<=0
InsertCycleToPath[graph_Graph,path_List,cycle_List,loop_Integer:1,opts:OptionsPattern[]]:=With[{ToVertex=(If[#===Length[path]+1,path[[-1,-1]],path[[#,1]]]&),cycles$len2=OptionValue["2-cycle"]},If[!AllTrue[Tally[Level[cycle,{2}]],#[[2]]==2&],Print["Not simple cycle."];Return[]];
Union[Flatten[Table[Flatten@Insert[path,bridge,$i]//.{a___,e_[b_,c_],e_[c_,b_],d___}/;FreeQ[cycles$len2,e[b,c]]:>{a,d},{$i,Length[path]+1},{bridge,FindCycleBridge[graph,cycle,ToVertex[$i],ToVertex[$i]]}],1]]]/;loop>0
InsertCycleToPath[graph_Graph,path_List,cycle_List,loop_Integer,opts:OptionsPattern[]]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&)},If[loop==0,{path},InsertCycleToPath[graph,path,ReverseThisPath@cycle,-loop,opts]]]/;loop<=0


ToCurveWord[graph_Graph,curve_List]:=With[{edge$names=With[{edgelabels=Join[AnnotationValue[graph,EdgeLabels],(#->"")&/@Complement[EdgeList[graph],AnnotationValue[graph,EdgeLabels][[All,1]]]]},Join[edgelabels,edgelabels/.$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i]],vertex$pos=Thread[VertexList[graph]->GraphEmbedding[graph]],edge$head=UndirectedEdge|DirectedEdge},
With[{LeftOrRight=({edge$in,edge$out}|->With[{ToVec=(#[[2]]-#[[1]]/.vertex$pos&),another$out=DeleteCases[Cases[edge$names[[All,1]],edge$head[edge$out[[1]],_]],edge$out|edge$head[_,edge$in[[1]]]][[1]]},If[SignedVectorAngle[ToVec@edge$in,ToVec@edge$out]>SignedVectorAngle[ToVec@edge$in,ToVec@another$out],"Left","Right"]])},
With[{ToMountainscape=(path|->Table[{path[[$i]]/.edge$names,{path[[$i]],If[$i<Length[path],Tooltip["Next",path[[$i+1]],BaseStyle->GrayLevel[2/3]],Nothing]},If[$i<Length[path],LeftOrRight[path[[$i]],path[[$i+1]]],"Fixed"]},{$i,Length[path]}])},
If[Head[curve[[1]]]===List,ToMountainscape/@curve,ToMountainscape@curve]/.{{y_,{e_[b_,c:Except[Subscript["p"|"V",__]]],d___},str_String}:>{y,{e[b,c],d}," "}}]]]


CurveWordToMatrix[curvewords_List]:=With[{curve$matrices=(curvewords/.{{y_,_,"Left"}:>{{y,y},{0,1}},{y_,_,"Right"}:>{{y,0},{1,1}},{__,"Fixed"|" "}->Nothing})},
Apply[Dot,curve$matrices,{Length[FirstPosition[curvewords,"Left"|"Right"|"Fixed",Print["Direction not found."];{1,3}]]-2}]]


CurveMatrixToVariable[curvematrix_List]:=With[{MatrixToU=(#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&),ChopTo1=(If[Chop[#1-1/.Table[ys->RandomReal[{0.2,0.8}],{ys,Union@Cases[#1,Subscript[y,__],\[Infinity]]}]/.#2->100,10^-5]==0,1,#1]&),CheckLimit=(If[MatchQ[#,0|\[Infinity]|ComplexInfinity],Print["Limit error? ",curvematrix];#,#]&)},Switch[ArrayDepth[curvematrix],2,MatrixToU[curvematrix],3,Switch[Length[curvematrix],2,
With[{diag2=Diagonal[curvematrix[[2]]],nondiag2=curvematrix[[2]]-DiagonalMatrix[Diagonal[curvematrix[[2]]]]},Module[{m},Simplify[CheckLimit[Factor[ChopTo1[MatrixToU[curvematrix[[1]] . (DiagonalMatrix[diag2^m]+(diag2[[2]]^m-diag2[[1]]^m)nondiag2/(diag2[[2]]-diag2[[1]]))],m]]/.{_^m->0}]]]],3,
With[{diag1=Diagonal[curvematrix[[1]]],nondiag1=curvematrix[[1]]-DiagonalMatrix[Diagonal[curvematrix[[1]]]],diag3=Diagonal[curvematrix[[3]]],nondiag3=curvematrix[[3]]-DiagonalMatrix[Diagonal[curvematrix[[3]]]]},Module[{m},Simplify[CheckLimit[Factor[ChopTo1[MatrixToU[(DiagonalMatrix[diag1^m]+(diag1[[2]]^m-diag1[[1]]^m)nondiag1/(diag1[[2]]-diag1[[1]])) . curvematrix[[2]] . (DiagonalMatrix[diag3^m]+(diag3[[2]]^m-diag3[[1]]^m)nondiag3/(diag3[[2]]-diag3[[1]]))],m]]/.{_^m->0}]]]],_,Print["Error input."];Return[]],_,Print["Error input."];Return[]]]


SelfIntersectionCount[curveword_List]:=With[{word=Join[{{"y",{"Begin1"\[UndirectedEdge]curveword[[1,2,1,1]]},"Fixed"}},curveword,{{"y",{curveword[[-1,2,1,-1]]\[UndirectedEdge]"End1"},"Fixed"}}],word$rev=Join[{{"y",{"Begin2"\[UndirectedEdge]curveword[[-1,2,1,-1]]},"Fixed"}},Table[{curveword[[-$i,1]],curveword[[-$i,2,;;1]]/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i},If[$i==Length[curveword],"Fixed",curveword[[-$i-1,3]]/.{"Left"->"Right","Right"->"Left"}]},{$i,Length[curveword]}],{{"y",{curveword[[1,2,1,1]]\[UndirectedEdge]"End2"},"Fixed"}}]},
With[{path=word[[All,2,1]],path$rev=word$rev[[All,2,1]],FirstDifferencePosition=(With[{size=Min[Length[#1],Length[#2]]},FirstPosition[Inner[SameQ,#1[[;;size]],#2[[;;size]],List],False,{size},{1}][[1]]]&),ToBraids=({$word,beginlens}|->If[MatchQ[beginlens,{}|{{}}],{},$word[[#[[1]]-1;;#[[1]]+#[[2]]-1,-1]]&/@beginlens]),ToSIcount=(braids|->If[braids==={},0,With[{braids$sort=Sort[PadRight[#,Max[Length/@braids],"None"]&/@braids/.{"Fixed"|" "->"None"},{list1,list2}|->FirstCase[Inner[Switch[{#1,#2},{"None",_}|{_,"None"},0,_,Order[#1,#2]]&,list1,list2,List],Except[0],Order[list1,list2]]]},Sum[Count[col[[pos;;]],"Left"],{col,braids$sort\[Transpose]},{pos,Position[col,"Right",{1}][[All,1]]}]]])},
Sum[With[{begins=Select[Position[path,path[[$i]],{1}][[All,1]],#>$i&&path[[$i-1]]=!=path[[#-1]]&],begins$rev=Select[Position[path$rev,path[[$i]],{1}][[All,1]],Length[path]-#+1>$i&&path[[$i-1]]=!=path$rev[[#-1]]&]},With[{lens=Table[FirstDifferencePosition[path[[$i;;]],path[[$j;;]]]-1,{$j,begins}],lens$rev=Table[FirstDifferencePosition[path[[$i;;]],path$rev[[$j;;]]]-1,{$j,begins$rev}]},ToSIcount@Join[If[Join[begins,begins$rev]==={},{},ToBraids[word,{{$i,Max[lens,lens$rev]}}]],ToBraids[word,{begins,lens}\[Transpose]],ToBraids[word$rev,{begins$rev,lens$rev}\[Transpose]]]]],{$i,Length[path]}]]]
SelfIntersectionCount[graph_Graph,curve_List]:=SelfIntersectionCount[ToCurveWord[graph,curve]]


Options[HightlightSurfaceCurve]={ImageSize->Medium,"L/R Label"->"Left/Right"};
HightlightSurfaceCurve[graph_Graph,path_List,opts:OptionsPattern[]]:=HighlightGraph[graph,Table[Style[Labeled[labelededge[[1,1]],(Style[StringJoin@@Riffle[#,","],Blue,Bold,10]&/@(labelededge[[All,2;;]]\[Transpose]))/.{{a_}:>a,{a_,b_}:>Labeled[a,b]}/.str_String/;If[OptionValue["L/R Label"]==="L/R",True,StringContainsQ[str,","]]:>StringReplace[str,{"Left"->"L","Right"->"R"}]],Red,Thick],{labelededge,GatherBy[If[Head[path[[1]]]===List,Table[{path[[$i,2,1]],ToString[$i],path[[$i,3]]},{$i,Length[path]}],Table[{path[[$i]],ToString[$i]},{$i,Length[path]}]],Sort@*First]}],Sequence@@FilterRules[Join[{opts},Options[HightlightSurfaceCurve]],Options[HighlightGraph]]]


(************************ 6. Functions Part V ***********************)


Options[FeynGraph$1Loop]={"Scaffolding"->True,"Notation"->{"y"->"Curve","V"->"Sequence"},"Output"->Graph};
FeynGraph$1Loop[n_Integer,opts:OptionsPattern[]]:=With[{circleLayout=({r,m,\[Theta],del}|->Delete[Table[{r Cos[2\[Pi] i/m+\[Theta]],-r Sin[2\[Pi] i/m+\[Theta]]},{i,0,m-1}],del]),toGraph=(OptionValue["Output"][#1,#2[[All,1]],{EdgeLabels->(#2/.Labeled->Rule),With[{toPos=(Switch[Mod[Round[2ArcTan@@#1/\[Pi]]+#2,4],0,After,1,Above,2,Before,3,Below]&)},VertexLabels->Table[vc[[1]]->Placed[vc[[1]],Switch[vc[[1]],Subscript["p",_],toPos[vc[[2]],0],Subscript["p",_,_],toPos[vc[[2]],If[n>3,1,0]],Subscript["V",__],toPos[vc[[2]],1](*Tooltip*)]],{vc,#3[[2]]}]],##3}]&),VyRenameRule=If[Association[OptionValue["Notation"]]["V"]==="Curve",{{Subscript["V", i_]:>Subscript["V", Mod[2i-1,2n,1],Mod[2i+1,2n,1],Subscript["L", 1]],Subscript[y, i_]:>Subscript[y, i,Subscript["L", 1]],DirectedEdge->UndirectedEdge},{Subscript["V", i_]:>Subscript["V", Mod[i,n,1],Mod[i+1,n,1],Subscript["L", 1]],Subscript[y, i_]:>Subscript[y, i,Subscript["L", 1]]}},{{},{}}]},If[OptionValue["Scaffolding"],
Once[toGraph[Join[Table[Subscript["p",i],{i,2n}],Table[Subscript["p",2i-1,2i],{i,n}],Table[Subscript["V",i],{i,n}]]/.VyRenameRule[[1]],Join[Table[Labeled[Subscript["V",Mod[-1+i,n,1]]\[DirectedEdge]Subscript["V",i],Subscript[y,i]],{i,n}],Table[Labeled[Subscript["p",2i-1]\[UndirectedEdge]Subscript["p",2i-1,2i],Subscript[y,2i-1,Mod[2i,2n,1]]],{i,n}],Table[Labeled[Subscript["p",2i]\[UndirectedEdge]Subscript["p",2i-1,2i],Subscript[y,2i,Mod[2i+1,2n,1]]],{i,n}],Table[Labeled[Subscript["p",2i-1,2i]\[UndirectedEdge]Subscript["V",i],Subscript[y,2i-1,Mod[2i+1,2n,1]]],{i,n}]]/.yRenameRules[n,Sequence@@FilterRules[{opts},Options[ytozRules]]]["1-Loop Scaffolding"]/.VyRenameRule[[1]],VertexCoordinates->Join[Thread[Table[Subscript["p",i],{i,2n}]->circleLayout[7/2,3n,-\[Pi]/(3n),List/@(3Range[n])]],Thread[Table[Subscript["p",2i-1,2i],{i,n}]->circleLayout[5/2,n,0,{}]],Thread[Table[Subscript["V",i]/.VyRenameRule[[1]],{i,n}]->circleLayout[1,n,0,{}]]]]],
Once[toGraph[Join[Table[Subscript["p",i],{i,n}],Table[Subscript["V",i],{i,n}]],Join[Table[Labeled[Subscript["V",Mod[i-1,n,1]]\[DirectedEdge]Subscript["V",i],Subscript[y,i]],{i,n}],Table[Labeled[Subscript["p",i]\[UndirectedEdge]Subscript["V",i],Subscript[y,i,Mod[i+1,n,1]]],{i,n}]],VertexCoordinates->Join[Thread[Table[Subscript["p",i],{i,n}]->circleLayout[5/2,n,0,{}]],Thread[Table[Subscript["V",i],{i,n}]->circleLayout[1,n,0,{}]]]]]]]


uCyclesRaw[graph_Graph,1]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&),RotateSortCycle=(cyc|->RotateLeft[cyc,OrderingBy[cyc,{Count[#[[1]],"L",\[Infinity]],Plus@@Cases[#[[1]],_Integer,\[Infinity]]}&][[1]]-1])},SortBy[Union[RotateSortCycle/@Join[FindCycle[graph,\[Infinity],All],ReverseThisPath/@FindCycle[graph,\[Infinity],All]]],Union[#/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]
uCyclesRaw[graph_Graph,loop_Integer]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&),RotateSortCycle=(cyc|->RotateLeft[cyc,OrderingBy[cyc,{Count[#[[1]],"L",\[Infinity]],Plus@@Cases[#[[1]],_Integer,\[Infinity]]}&][[1]]-1]),cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&]},
SortBy[Union[RotateSortCycle/@DeleteCases[Join[uCyclesRaw[graph,loop-1],Flatten[Table[If[DisjointQ[Level[cyc1,{2}],Level[cyc2,{2}]]||MatchQ[cyc1,{a___,Sequence@@ReverseThisPath@cyc2,d___}],Nothing,InsertCycleToPath[cyc1,cyc2,1,"2-cycle"->cycles$len2]],{cyc1,uCyclesRaw[graph,loop-1]},{cyc2,uCyclesRaw[graph,1]}],2]],{}|{a___,e_[b_,c_],e_[c_,b_],d___}|{e_[c_,b_],a___,e_[b_,c_]}/;FreeQ[cycles$len2,e[b,c]]]],Union[#/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]/;loop>1


Options[uPathsRaw]={"Scaffolding"->True,"Surfacehedron"->"Dn\[Infinity]"};
uPathsRaw[graph_Graph,aa_Integer,bb_Integer,0,OptionsPattern[]]:=SortBy[Union@FindAllPathsInEdges[graph,Subscript["p",aa],Subscript["p",bb]],Union[#/.UndirectedEdge->(Sort@*List)]&]/;(!OptionValue["Scaffolding"]||Ceiling[aa/2]!=Ceiling[bb/2])&&aa!=bb
uPathsRaw[graph_Graph,aa_Integer,bb_Integer,loop_Integer:1,opts:OptionsPattern[]]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&),cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&]},
SortBy[Union[DeleteCases[Join[uPathsRaw[graph,aa,bb,loop-1,opts],Flatten[Table[If[DisjointQ[Level[path,{2}],Level[cyc,{2}]]||MatchQ[path,{a___,Sequence@@ReverseThisPath@cyc,d___}],Nothing,InsertCycleToPath[path,cyc,1,"2-cycle"->cycles$len2]],{path,uPathsRaw[graph,aa,bb,loop-1,opts]},{cyc,uCyclesRaw[graph,1]}],2]],{}|{a___,e_[b_,c_],e_[c_,b_],d___}/;FreeQ[cycles$len2,e[b,c]]]],Union[#/.UndirectedEdge->(Sort@*List)]&]]/;(!OptionValue["Scaffolding"]||Ceiling[aa/2]!=Ceiling[bb/2])&&aa!=bb&&loop>0
uPathsRaw[graph_Graph,aa_Integer,bb_Integer,loop_Integer:1,opts:OptionsPattern[]]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&),RotateToBeginning=(RotateLeft[#1,FirstPosition[#1,#2][[1]]-1]&),cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&]},
SortBy[DeleteDuplicatesBy[DeleteCases[Flatten[Table[Join[path1,RotateToBeginning[cyc,vert\[UndirectedEdge]_],path2],{cyc,uCyclesRaw[graph,loop]},{vert,cyc[[All,1]]},{path1,FindAllPathsInEdges[graph,Subscript["p",aa],vert]},{path2,FindAllPathsInEdges[graph,vert,Subscript["p",bb]]}],3]//.{a___,e_[b_,c_],e_[c_,b_],d___}/;FreeQ[cycles$len2,e[b,c]]:>{a,d},{}],Sort[{#,ReverseThisPath@#}]&],Union[#/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]/;((OptionValue["Scaffolding"]&&Ceiling[aa/2]==Ceiling[bb/2])||aa==bb)&&loop>0
uPathsRaw[graph_Graph,aa_Integer,Subscript["L",bb_Integer],0,OptionsPattern[]]:=With[{fund$cycle=Select[uCyclesRaw[graph,1],NoneTrue[Union@Cases[#,Subscript["V",__],{2}],FreeQ[Subscript["L",bb]]]&&FreeQ[ToCurveWord[graph,#],"Right"]&][[1]],cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&]},
SortBy[Union[DeleteCases[Flatten[Table[{#,RotateLeft[fund$cycle,$i-1]}&/@FindAllPathsInEdges[graph,Subscript["p",aa],fund$cycle[[$i,1]]],{$i,Length[fund$cycle]}],1],({{a___,e_[b_,c_]},{e_[c_,b_],d___}}/;FreeQ[cycles$len2,e[b,c]])|{{a___,b_},{c___,b_}}]],Union[#[[1]]/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]
uPathsRaw[graph_Graph,aa_Integer,Subscript["L",bb_Integer],loop_Integer:1,opts:OptionsPattern[]]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&),cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&]},
SortBy[Union[DeleteCases[Join[uPathsRaw[graph,aa,Subscript["L",bb],loop-1,opts],Flatten[Table[If[DisjointQ[Level[path[[1]],{2}],Level[cyc,{2}]]||MatchQ[path[[1]],{a___,Sequence@@ReverseThisPath@cyc,d___}],Nothing,{#,path[[2]]}&/@InsertCycleToPath[path[[1]],cyc,1,"2-cycle"->cycles$len2]],{path,uPathsRaw[graph,aa,Subscript["L",bb],loop-1,opts]},{cyc,uCyclesRaw[graph,1]}],2]],({{a___,e_[b_,c_],e_[c_,b_],d___},_}|{{a___,e_[b_,c_]},{e_[c_,b_],d___}}/;FreeQ[cycles$len2,e[b,c]])|{{a___,b_},{c___,b_}}|{}]],Union[#[[1]]/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]/;loop>0
uPathsRaw[graph_Graph,Subscript["L",aa_Integer],Subscript["L",bb_Integer],0,OptionsPattern[]]:=With[{fund$cyc1=Select[uCyclesRaw[graph,1],NoneTrue[Union@Cases[#,Subscript["V",__],{2}],FreeQ[Subscript["L",aa]]]&&FreeQ[ToCurveWord[graph,#],"Left"]&][[1]],fund$cyc2=Select[uCyclesRaw[graph,1],NoneTrue[Union@Cases[#,Subscript["V",__],{2}],FreeQ[Subscript["L",bb]]]&&FreeQ[ToCurveWord[graph,#],"Right"]&][[1]],cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&],cycleToStdRule={{{a_,b_,c___},{a_,b_,d___},e_}:>{{b,c,a},{b,d},e},{e_,{c___,a_,b_},{d___,a_,b_}}:>{e,{c,a},{b,d,a}},{{a_,b_,c___},{a_},{b_,d___}}:>{{b,c,a},{b},{d,b}},{{c___,a_},{b_},{d___,a_,b_}}:>{{a,c},{a},{b,d,a}},{{c___,a_},{},{d___,a_}}:>{{a,c},{a},{d,a}},{{a_,c___},{},{a_,d___}}:>{{a,c},{a},{d,a}}}},
SortBy[Union[DeleteCases[Flatten[Table[{RotateLeft[fund$cyc1,$i-1],#,RotateLeft[fund$cyc2,$j-1]}&/@FindAllPathsInEdges[graph,fund$cyc1[[$i,1]],fund$cyc2[[$j,1]]],{$i,Length[fund$cyc1]},{$j,Length[fund$cyc2]}],2]//.cycleToStdRule,{{a___,e_[b_,c_]},{e_[c_,b_],d___},_}|{_,{a___,e_[b_,c_]},{e_[c_,b_],d___}|{_,{a___,e_[b_,c_],e_[c_,b_],d___},_}}/;FreeQ[cycles$len2,e[b,c]]]//.{{{a1_,c___,b_},{a2_,d___},e_}/;a1=!=a2:>{{b,a1,c},{b,a2,d},e},{e_,{d___,a2_},{b_,c___,a1_}}/;a1=!=a2:>{e,{d,a2,b},{c,a1,b}}}],Union[#[[2]]/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]/;aa!=bb
uPathsRaw[graph_Graph,Subscript["L",aa_Integer],Subscript["L",bb_Integer],loop_Integer:1,opts:OptionsPattern[]]:=With[{ReverseThisPath=(Reverse[#/.{$i_\[UndirectedEdge]$j_:>$j\[UndirectedEdge]$i,$i_\[DirectedEdge]$j_:>$j\[DirectedEdge]$i}]&),RotateToBeginning=(RotateLeft[#1,FirstPosition[#1,#2][[1]]-1]&),ReduceToNoIntersection=(chain|->With[{inters=Alternatives@@Union[Level[chain[[2]],{2}]]},FixedPoint[If[#[[1]]==={}||FreeQ[#[[1,1]],inters],If[#[[3]]==={}||FreeQ[#[[3,-1]],inters],#,{#[[1]],#[[2]],#[[3,;;-2]]}],{#[[1,2;;]],#[[2]],#[[3]]}]&,chain,Length[chain[[1]]]+Length[chain[[3]]]]]),cycles$len2=Select[uCyclesRaw[graph,1],Length[#]==2&],cycleToStdRule={{{a_,b_,c___},{a_,b_,d___},e_}:>{{b,c,a},{b,d},e},{e_,{c___,a_,b_},{d___,a_,b_}}:>{e,{c,a},{b,d,a}},{{a_,b_,c___},{a_},{b_,d___}}:>{{b,c,a},{b},{d,b}},{{c___,a_},{b_},{d___,a_,b_}}:>{{a,c},{a},{b,d,a}},{{c___,a_},{},{d___,a_}}:>{{a,c},{a},{d,a}},{{a_,c___},{},{a_,d___}}:>{{a,c},{a},{d,a}}}},
SortBy[Union[DeleteCases[Join[uPathsRaw[graph,Subscript["L",aa],Subscript["L",bb],loop-1,opts],Flatten[Table[If[DisjointQ[Level[Join@@path,{2}],Level[cyc,{2}]]||MatchQ[Join@@path,{a___,Sequence@@ReverseThisPath@cyc,d___}],Nothing,{RotateToBeginning[path[[1]],#[[1,1]]\[UndirectedEdge]_],#,RotateToBeginning[path[[3]],#[[-1,-1]]\[UndirectedEdge]_]}&/@DeleteCases[InsertCycleToPath[Join@@ReduceToNoIntersection[path],cyc,1,"2-cycle"->cycles$len2],{}]],{path,uPathsRaw[graph,Subscript["L",aa],Subscript["L",bb],loop-1,opts]},{cyc,uCyclesRaw[graph,1]}],2]]//.cycleToStdRule,{{a___,e_[b_,c_]},{e_[c_,b_],d___},_}|{_,{a___,e_[b_,c_]},{e_[c_,b_],d___}|{_,{a___,e_[b_,c_],e_[c_,b_],d___},_}}/;FreeQ[cycles$len2,e[b,c]]]//.{{{a1_,c___,b_},{a2_,d___},e_}/;a1=!=a2:>{{b,a1,c},{b,a2,d},e},{e_,{d___,a2_},{b_,c___,a1_}}/;a1=!=a2:>{e,{d,a2,b},{c,a1,b}}}],Union[#[[2]]/.UndirectedEdge|DirectedEdge->(Sort@*List)]&]]/;aa!=bb&&loop>0


Options[uPaths]={"Scaffolding"->True,"Surfacehedron"->"Dn\[Infinity]","SI"->Automatic};
uPaths[graph_Graph,aa_Integer,bb_Integer,loop_Integer:1,opts:OptionsPattern[]]:=With[{maxSI=If[OptionValue["SI"]===Automatic,loop,OptionValue["SI"]]},
Select[ToCurveWord[graph,uPathsRaw[graph,aa,bb,loop,Sequence@@FilterRules[{opts},Options[uPathsRaw]]]],SelfIntersectionCount[#]<=maxSI&]]
uPaths[graph_Graph,aa_Integer,Subscript["L",bb_Integer],loop_Integer:1,opts:OptionsPattern[]]:=With[{maxSI=If[OptionValue["SI"]===Automatic,loop,OptionValue["SI"]],path$cycles=uPathsRaw[graph,aa,Subscript["L",bb],loop,Sequence@@FilterRules[{opts},Options[uPathsRaw]]]},
Select[Partition[ToCurveWord[graph,Flatten[{Append[#[[1]],#[[2,1]]],Append[#[[2]],#[[2,1]]]}&/@path$cycles,1]],2][[All,All,;;-2]],SelfIntersectionCount[Join@@#]<=maxSI&]]
uPaths[graph_Graph,Subscript["L",aa_Integer],Subscript["L",bb_Integer],loop_Integer:1,opts:OptionsPattern[]]:=With[{maxSI=If[OptionValue["SI"]===Automatic,loop,OptionValue["SI"]],cycle$path$cycles=uPathsRaw[graph,Subscript["L",aa],Subscript["L",bb],loop,Sequence@@FilterRules[{opts},Options[uPathsRaw]]]},
Select[Partition[ToCurveWord[graph,Flatten[{Append[#[[1]],#[[2,1]]],Append[#[[2]],#[[3,1]]],Append[#[[3]],#[[3,1]]]}&/@cycle$path$cycles,1]],3][[All,All,;;-2]],SelfIntersectionCount[Join@@#]<=maxSI&]]


Options[uPath]={"Scaffolding"->True,"Ordering"->"Clockwise","Notation"->{"y"->"Curve"}};
uPath[n_Integer,i_Integer,j_Integer,opts:OptionsPattern[]]:=Once[With[{thisVi=If[OptionValue["Scaffolding"],Ceiling[i/2],i],ReverseOrNot=If[OptionValue["Ordering"]==="Clockwise",{},{"Left"->"Right","Right"->"Left"}],ifcycle=(i==j||(i-j==1&&EvenQ[i]&&OptionValue["Scaffolding"])),graph=Once[FeynGraph$1Loop[n,Sequence@@FilterRules[{opts},Options[FeynGraph$1Loop]],"Output"->List]/.If[OptionValue["Ordering"]==="Clockwise",{},V1_\[DirectedEdge]V2_:>V2\[DirectedEdge]V1]]},
With[{edges=Once[List@@@graph[[3,1,2]]],pointPath=Once[If[!ifcycle,FindPath[Once[Graph@@graph],Subscript["p",i],Subscript["p",j],\[Infinity],All][[1]],If[FreeQ[#,{___,Subscript["V",a_],Subscript["V",b_],___}/;Mod[b-a-If[OptionValue["Ordering"]==="Clockwise",1,-1],n]==0],Reverse[#],#]&@Join[{Subscript["p",i],If[OptionValue["Scaffolding"],If[OddQ[i],Subscript["p",i,i+1],Subscript["p",i-1,i]],Nothing]},RotateLeft[#,Position[#,Subscript["V",thisVi]\[UndirectedEdge]_][[1,1]]-1]&@FindCycle[{Once[Graph@@(graph/.DirectedEdge->UndirectedEdge)],Subscript["V",thisVi]},\[Infinity],All][[1]]/.UndirectedEdge->Sequence,{If[OptionValue["Scaffolding"],If[OddQ[j],Subscript["p",j,j+1],Subscript["p",j-1,j]],Nothing],Subscript["p",j]}]//.{a___,b_,b_,c___}:>{a,b,c}]],
LeftOrRight=({#1,#2,Switch[#2,{Subscript["p",a_],Subscript["p",a_,b_],Subscript["V",_]},"Right",{Subscript["p",b_],Subscript["p",a_,b_],Subscript["V",_]},"Left",{Subscript["p",__],Subscript["V",_],Subscript["V",_]},"Left"/.ReverseOrNot,{Subscript["V",_],Subscript["V",_],Subscript["V",_]},"Right"/.ReverseOrNot,{Subscript["V",_],Subscript["V",_],Subscript["p",__]},"Left"/.ReverseOrNot,{Subscript["V",_],Subscript["p",a_,b_],Subscript["p",a_]},"Left",{Subscript["V",_],Subscript["p",a_,b_],Subscript["p",b_]},"Right",{Subscript["p",a_],Subscript["p",a_,b_],Subscript["p",b_]},"Left",{Subscript["p",b_],Subscript["p",a_,b_],Subscript["p",a_]},"Right",_,"Fixed"]}&)},
Table[LeftOrRight@@{Cases[Once[Union[edges,{Reverse[#[[1]]],#[[2]]}&/@Cases[edges,{_UndirectedEdge,_}]]],{_[pointPath[[$i]],pointPath[[$i+1]]],_}][[1,2]],If[$i<Length[pointPath]-1,{pointPath[[$i]],pointPath[[$i+1]],pointPath[[$i+2]]},{}]},{$i,Length[pointPath]-1}]]]]
uPath[n_Integer,SuperPlus[i_]|SuperMinus[j_],opts:OptionsPattern[]]:=With[{thisVi=If[OptionValue["Scaffolding"],Ceiling[(i+j)/2],i+j],upath=uPath[n,i,i,j,j,"Scaffolding"->OptionValue["Scaffolding"],"Ordering"->If[TrueQ[And[j]],"Clockwise","CounterClockwise"]],break=If[OptionValue["Scaffolding"],-3,-2]},Join[upath[[;;break-1]],{upath[[break]]/.{"Left"->"Right","Right"->"Left",Subscript["p",a_]:>Subscript["V",Mod[a+Sign[j/i],n,1]],Subscript["p",a_,b_]:>Subscript["V",Mod[b/2+Sign[j/i],n,1]]},{Subscript[y,Mod[thisVi+UnitStep[j/i],n,1]]/.yRenameRules[n,Sequence@@FilterRules[{opts},Options[ytozRules]]]["1-Loop Scaffolding"],{},"Fixed"}}]]


Options[uPolynomial]={"Scaffolding"->True,"Notation"->{"y"->"Curve"}};
uPolynomial[n_Integer,ij__Integer|k_SuperPlus|k_SuperMinus,opts:OptionsPattern[]]:=Once[#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&@(Dot@@(uPath[n,ij,k,opts]/.{{y_,_,"Left"}:>{{y,y},{0,1}},{y_,_,"Right"}:>{{y,0},{1,1}},{__,"Fixed"}->Nothing}/.{Subscript[y,a_,b_]/;Mod[b-a-1,If[OptionValue["Scaffolding"],2n,n]]==0->1}))]
uPolynomial[n_Integer,Subscript[i_,\[Infinity]]|Subscript[j_,-\[Infinity]],opts:OptionsPattern[]]:=Once[With[{uMatrices={Dot@@#1[[;;#2-1]],Dot@@#1[[#2;;]]}&@@{uPath[n,If[TrueQ[And[j]],SuperPlus[i],SuperMinus[j]],opts][[;;-2]]/.{{y_,_,"Left"}:>{{y,y},{0,1}},{y_,_,"Right"}:>{{y,0},{1,1}}}/.{Subscript[y,a_,b_]/;Mod[b-a-1,If[OptionValue["Scaffolding"],2n,n]]==0->1},If[OptionValue["Scaffolding"],3,2]}},
With[{diag2=Diagonal[uMatrices[[2]]],nondiag2=uMatrices[[2]]-DiagonalMatrix[Diagonal[uMatrices[[2]]]]},Module[{m},Simplify[Together[#[[1,2]]#[[2,1]]/(#[[1,1]]#[[2,2]])&@(uMatrices[[1]] . (DiagonalMatrix[diag2^m]+(diag2[[2]]^m-diag2[[1]]^m)nondiag2/(diag2[[2]]-diag2[[1]])))]//.{Times[a_^m,b__]+c_/;FreeQ[c,m]:>c,a_^m+c_/;FreeQ[c,m]:>c}]]]]]


Options[StringyIntegrand$XY]={"Scaffolding"->True,"Surfacehedron"->"Dn\[Infinity]"};
StringyIntegrand$XY[n_Integer,opts:OptionsPattern[]]:=Once[With[{m=If[OptionValue["Scaffolding"],2n,n]},PowerExpand[Product[If[#===0,1,#]&@uPolynomial[n,i,j,Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[X,i,j],{i,m},{j,m}]*
If[StringContainsQ[OptionValue["Surfacehedron"],"inf"|"\[Infinity]",IgnoreCase->True],Product[uPolynomial[n,Subscript[i,-\[Infinity]],Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[OverTilde[Y],i],{i,m}],Product[uPolynomial[n,SuperPlus[i],Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[Y,i],{i,m}]Product[uPolynomial[n,SuperMinus[i],Sequence@@FilterRules[{opts},Options[uPolynomial]]]^Subscript[OverTilde[Y],i],{i,m}]]/.a_Plus:>Factor[a]/.yRenameRules[n,Sequence@@FilterRules[{opts},Options[ytozRules]]]["1-Loop Scaffolding"]]]]


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
