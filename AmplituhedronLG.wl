(* ::Package:: *)

(* ::Chapter:: *)
(*Amplituhedron-Like Geometry*)


BeginPackage["AmplituhedronLG`",{"BraketsAuxiliary`"}]


(*In order to allow the package to be reloaded we unprotect and clear all the symbol definitions*)
Unprotect@@Names["AmplituhedronLG`*"];
ClearAll@@Names["AmplituhedronLG`*"];


(* ::Section:: *)
(*Function description*)


(* ::Subsection:: *)
(*Subscript[H, n,k,m]^(f,Subscript[n, m]) inequalities*)


AmplituhedronLikeG::usage="AmplituhedronLikeG[n,f,m,l,nfmin]"
SignFlipPatterns::usage="SignFlipPatterns[n,f,m, Tips : False]"
ProperBoundaries::usage="ProperBoundaries[n,f,m]"
LoopInequalities::usage="LoopInequalities[n,f,m,l,nfmin : 0]"


(* ::Subsection:: *)
(*Canonical Form,parametrization and  external data*)


CF::usage="CF[ineq,Y,Z,loops : {}]."
CFrule::usage="CFrule[expr]"
Parametrizebr::usage="Parametrizebr[ineq_,Y_,Z_,loops_List:{}]"
Zpositive::usage="Zpositive[n,k,m : 4]"
ZVander::usage="ZVander[n,k,m : 4]"
YI::usage="YI[k,m : 4, $sign-> {-,+}]"
Measure::usage="Measure[Y,m:4] gives the measure of Y"


(* ::Subsection:: *)
(*Known covariant covariant forms*)


R::usage="R[Z]."
NMHVR::usage="NMHVR[n,m : 4]"
NMHVmaximal::usage="N^(n-m)MHV    k = n+m."
NMHVsignFlips::usage="NMHV amplitude from signflip triangulation."
N2MHV7BCFW::usage="NMHVsignFlips[n]."
NMHVSQ::usage="NMHVSQ[n, m : 4]."
N2MHV7BCFW::usage "N2MHV7BCFW"
MHV::usage "MHV[n] give the n point 1 loop MHV amplitude"
MHV1loopsSquared::usage "MHV1loopsSquared contains the 4 point 1 loop MHV amplitude squared"
MHV2loops::usage "MHV2loops contains the 4 point 2 loop MHV amplitude"


(* ::Subsection:: *)
(*Product of bosonized brackets*)


StarProd::usage="StarProd[x,y,m:4] represent the product between two covariant forms in which there are grassman dependent brackets at the denominator. All brackets of length $mStar are considered scalars."
ExpandStarAndInter::usage="Expand star product and intersections."
prodBracketsToList::usage" Changes Times and br with List and Power with Table."

expandCapRule::usage="expandCapRule."
brIntersection::usage=" " 
StarProdExp::usage=" "
cap::usage=" "
cbr::usage=" "
$mStar::usage=" "
FormsProd::usage=" "
starProductscalarQ::usage=" "


(* ::Subsection::Closed:: *)
(*Graphics*)


graphSignFlipPatterns::"graphSignFlipPatterns[n,f,m : 4] Gives the allowed flipping patterns of the Subscript[H^(f), n,k] as a list of plus and minus.."
bello::"Similar to Traditional Form. Equivalent of Jake nice." 


(* ::Section:: *)
(*Private context starts here*)


Begin["`Private`"]


(*We define a private variable "frontend" needed for the package to decide whether to run shortcuts and the palette or not. This is related to the availability of a frontend.*)


(*frontend=If[TrueQ[$FrontEnd==Null],0,1];*)


(* ::Section::Closed:: *)
(*Amplituhedron like geometry inequalities*)


(* ::Input::Initialization:: *)
AmplituhedronLikeG[n_,f_,m_ ,l_ : 0, nfmin_ : 0]:=And[LoopInequalities[n,f,m,l,nfmin],ProperBoundaries[n,f,m],SignFlipPatterns[n,f,m]]/; f<=  n-m

SignFlipPatterns[n_,f_,m_, Tips_ : False]:=Module[{temp},
If[f>  n-m,Return[$Failed]];
temp=Append[#,(-1)^Boole[EvenQ[m]&&OddQ[f]]]&/@(Permutations[Join[Table[-1,{i,f}],Table[1,{i,n-m-f}]]]);
temp=#>0&/@Inner[Times,Table[br[Append[Range[m-1],i]],{i,m,n}],#,List] &/@(Table[Times@@Take[#,i],{i,Length[#]-1}]&/@(Prepend[#,(-1)^Boole[OddQ[m]&&OddQ[f]]]&/@temp));
If[Tips,Or@@And@@@temp, Or@@And@@@(Delete[#,{{1},{-1}}]&/@temp)]
]
ProperBoundaries[n_,f_,m_]:=Module[{temp1,temp2,z},
If[EvenQ[m],
And@@(#>0&/@(DeleteDuplicates@ DeleteCases[(br/@Flatten/@Subsets[Subsequences[Append[Range[n],(-1)^(f+1) z[1]],{2}],{m/2}])/.z[1]-> 1,0])),
		temp1=Prepend[#,(-1)^f z[1]]&/@(Flatten/@Subsets[Subsequences[Range[2,n],{2}],{(m-1)/2}]);
	temp2=Append[#,n]&/@(Flatten/@Subsets[Subsequences[Range[1,n-1],{2}],{(m-1)/2}]);
And@@(#>0&/@DeleteCases[(br/@Join[temp1,temp2])/.z[1]-> 1,0])
]
];


LoopInequalities[n_,f_,m_,l_,nfmin_ : 0]:=Module[{mutual,oneloopfMax,oneloopfMin},
If[nfmin>l,Print["nfmin= ",nfmin, " cannot be bigger then l=", l];Return[$Failed]];
If[l===0,Return[True]];
If[OddQ[m]||m<3,Return[$Failed]];

mutual=And@@(#>0&/@br@@@Subsets[Range[l],{2}]/.br[i_,j_]:>  br[{A[i],B[i],A[j],B[j]}]);
oneloopfMax=If[nfmin===l,{},Join[AmplituhedronLikeG[n,f+2,m-2]/.({br[{x__}]:> br[{A[#],B[#],x}]}&/@Range[l-nfmin])]];
oneloopfMin=If[nfmin===0,{},Join[AmplituhedronLikeG[n,f,m-2]/.({br[{x__}]:> br[{A[#],B[#],x}]}&/@Range[l-nfmin+1,l])]];
And[And@@Join[oneloopfMin,oneloopfMax],mutual]
]




(* ::Section::Closed:: *)
(*Canonical Form, parametrization and  external data*)


Clear[CF,CFrule,Parametrizebr,Zpositive,AddPositiveColumn,ZVander,YI]

CF[ineq_,Y_,Z_,loops_List : {}]:= CFrule@(GenericCylindricalDecomposition[#,Reduce`FreeVariables[#]][[1]]&@Parametrizebr[ineq,Y,Z,loops]);

CFrule[expr_]:= expr /.Less[a_,b_]:> 1/(b-a)/.Greater[a_,b_]:> 1/(a-b)/.Less[a_,b_,c_]:> 1/(b-a)-1/(b-c)/.Greater[a_,b_,c_]:> -(1/(b-a))+1/(b-c)/.Inequality[a_,Less,b_,Less,c_]:> 1/(b-a)-1/(b-c)/.Inequality[a_,Greater,b_,Greater,c_]:> -(1/(b-a))+1/(b-c)/.And->Times/.Or->Plus


(*
Parametrizebr[ineq_,Y_,Z_]:=Module[{z,m},
If[Y!= {}&&(Length[Transpose@Y]!=Length[Transpose@Z]),
Return[Print["No matching dimensions betweeen Z and Y"]],
m=Length@Transpose@Z-Length@Y;
z[i_]:=Z[[i]];
z[A[i_]]:= {1,0,aa[i,1],aa[i,2]} . (Z[[#]]&/@Range[m]);
z[B[i_]]:= {0,1,bb[i,1],bb[i,2]} . (Z[[#]]&/@Range[m]);
ineq/. br[x__]/; Length[x]===m:>  Det[Join[Y,z/@x]] /. br[x__]:>  Det[z/@x] 
]
]
*)
Parametrizebr[ineq_,Y_,Z_,loops_List:{}]:=Module[{z,m},
If[Y!= {}&&(Length[Transpose@Y]!=Length[Transpose@Z]),
Return[Print["No matching dimensions betweeen Z and Y"]],
m=Length@Transpose@Z-Length@Y;
z[i_]:=Z[[i]];
z[A[i_]]:= loops[[i,1]];
z[B[i_]]:= loops[[i,2]];
ineq/. br[x__]/; Length[x]===m:>  Det[Join[Y,z/@x]] /. br[x__]:>  Det[z/@x] 
]
]


Zpositive[n_,k_,m_ : 4]:=Nest[AddPositiveColumn,IdentityMatrix[k+m],n-k-m]

AddPositiveColumn[M_]:=Module[{newC,cc},
newC=cc/@Range[Length[Transpose@M]];
newC=newC/. FindInstance[#>0&/@Flatten[Minors[Append[M,newC],Length[Transpose@M]]],newC,Integers][[1]];
newC=newC/(Times@@Intersection@@Divisors[newC]);
Append[M,newC]
]


ZVander[n_,k_,m_ : 4]:= Module[{a},
a=NestList[#+1&,1,n-1];
NestList[# # &,a,k+m-1]]

Options[YI]= {$sign-> $sign0};
YI[k_,m_ : 4, OptionsPattern[]]:=If[OptionValue[$sign]==="-",Join[Table[-1 KroneckerDelta[1,i],{i,k}]IdentityMatrix[k],Table[Global`cc[i,j],{i,k},{j,m}],2], Join[IdentityMatrix[k],Table[Global`cc[i,j],{i,k},{j,m}],2]]
YI[0,m_ : 4, OptionsPattern[]]:= {}


VarSelect[Y_,m_:4]:= Module[{freeYvar,Ypar,opts,tempfreevar},
freeYvar=Map[Reduce`FreeVariables,Y,{1}];
Ypar={};
Do[opts=Subsets[freeYvar[[-1]],{m}];
PrependTo[Ypar,Do[ tempfreevar=Complement[#,opts[[i]]]&/@Drop[freeYvar,-1];If[And@@(Length[#]>(m-1)&/@tempfreevar),Return[opts[[i]]]], {i,Length[opts]}]];
freeYvar=tempfreevar;
,{j,Length[freeYvar]}];
Ypar
]
Measure[Y_,m_:4]:= Module[{var=VarSelect[Y,m],gradients},
gradients=Table[D[Y[[i]],{var[[i]]}],{i,Length[Y]}];
Times@@(Det[Join[Y,Transpose[#]]]&/@gradients)
]


(* ::Section::Closed:: *)
(*Known covariant covariant forms*)


R[a__]:= br[a]^(Length[a]-1)/(Times@@(br[Drop[#,-1]]&/@NestList[RotateRight,a,Length[a]-1]))

NMHVR[n_,m_ : 4]:=Plus@@(R/@(Prepend[#,1]&/@Nest[uniqueTuples[#,Subsequences[Range[2,n],{2}]]&,Subsequences[Range[2,n],{2}],m/2-1]))/;EvenQ[m]


NMHVsignFlips[n_]:= 
Module[{rangej,rangei,temp,c},
c=Mod[#,n,1]&;
rangej=Delete[Range[n],{{1},{2},{3},{5}}];
rangei[j_]:= Delete[Range[n],{{j-2},{j-1},{j},{c[j+1]}}];
-Sum[(br[{1,2,3,5,j}]br[{j-1,j,c[j+1],i,c[i+1]}]^3)/(br[{1,2,3,5}]br[{j-1,j,c[j+1],i}]br[{j-1,j,c[j+1],c[i+1]}]br[{j-1,j,i,c[i+1]}]br[{j,c[j+1],i,c[i+1]}])
,{j,rangej},{i,rangei[j]}]
]


NMHVmaximal[n_, m_ : 4]:=br[Range[n]]^m/Times@@(br[#]&/@ Subsequences[Join[Range[n],Range[m-1]],{m}]) /; m< n


NMHVSQ[n_, m_ : 4]:=Expand[NMHVR[n,m]^2]/. br[x__]^(2 m)-> 0 /. ProdRule[m]


MHV[n_]:= 
Module[{flipPosition},
flipPosition=Flatten[Table[{i,j},{i,2,n-2},{j,i+1,n-1}],1];
Apply[(br[{A[1],1,#1,#1+1}]br[{B[1],1,#2,#2+1}]-br[{B[1],1,#1,#1+1}]br[{A[1],1,#2,#2+1}])^2/(br[{A[1],B[1],1,#1}]br[{A[1],B[1],1,#1+1}]br[{A[1],B[1],#1,#1+1}]br[{A[1],B[1],1,#2}]br[{A[1],B[1],1,#2+1}]br[{A[1],B[1],#2,#2+1}])&,flipPosition,{1}]
]


MHV1loopsSquared=br[{1,2,3,4}]^4/(br[{1,2,A[1],B[1]}] br[{1,2,A[2],B[2]}] br[{1,4,A[1],B[1]}] br[{1,4,A[2],B[2]}] br[{2,3,A[1],B[1]}] br[{2,3,A[2],B[2]}] br[{3,4,A[1],B[1]}] br[{3,4,A[2],B[2]}]);


MHV2loops =-(br[{1,2,3,4}]^3/(br[{1,2,A[2],B[2]}] br[{1,4,A[1],B[1]}] br[{1,4,A[2],B[2]}] br[{2,3,A[1],B[1]}] br[{2,3,A[2],B[2]}] br[{3,4,A[1],B[1]}] br[{A[1],A[2],B[1],B[2]}]))-br[{1,2,3,4}]^3/(br[{1,2,A[1],B[1]}] br[{1,4,A[1],B[1]}] br[{1,4,A[2],B[2]}] br[{2,3,A[1],B[1]}] br[{2,3,A[2],B[2]}] br[{3,4,A[2],B[2]}] br[{A[1],A[2],B[1],B[2]}])-br[{1,2,3,4}]^3/(br[{1,2,A[1],B[1]}] br[{1,2,A[2],B[2]}] br[{1,4,A[2],B[2]}] br[{2,3,A[1],B[1]}] br[{3,4,A[1],B[1]}] br[{3,4,A[2],B[2]}] br[{A[1],A[2],B[1],B[2]}])-br[{1,2,3,4}]^3/(br[{1,2,A[1],B[1]}] br[{1,2,A[2],B[2]}] br[{1,4,A[1],B[1]}] br[{2,3,A[2],B[2]}] br[{3,4,A[1],B[1]}] br[{3,4,A[2],B[2]}] br[{A[1],A[2],B[1],B[2]}]);


uniqueTuples[a_List,b_List]:=Module[{f},f[___,x_,x_,___]=Sequence[];
f[x_,y__]:=(f[x,y]=Sequence[];{x,y});
SetAttributes[f,Orderless];
Flatten[Outer[f@@Flatten[{##}]&,a,b,1],1]]

N2MHV7BCFW= Plus@@{((br[{1,3,4,5}] br[{1,2,4,5,6,7}]-br[{1,2,4,5}] br[{1,3,4,5,6,7}])^4/(br[{1,2,3,4}] br[{1,2,4,5}] br[{1,3,4,5}] br[{1,4,5,6}] br[{1,4,5,7}] br[{1,5,6,7}] (br[{1,2,3,5}] br[{1,4,6,7}]-br[{1,2,3,4}] br[{1,5,6,7}]) br[{2,3,4,5}] br[{4,5,6,7}])),-(br[{1,3,6,7}] br[{1,2,4,5,6,7}]-br[{1,2,6,7}] br[{1,3,4,5,6,7}])^4/(br[{1,2,3,7}] br[{1,2,6,7}] br[{1,3,6,7}] br[{1,4,6,7}] br[{1,5,6,7}] (br[{1,2,3,5}] br[{1,4,6,7}]-br[{1,2,3,4}] br[{1,5,6,7}]) (br[{1,5,6,7}] br[{2,3,4,6}]-br[{1,4,6,7}] br[{2,3,5,6}]) br[{4,5,6,7}]),-((br[{2,3,6,7}] br[{1,2,3,4,5,6}]-br[{1,2,3,6}] br[{2,3,4,5,6,7}])^4/(br[{1,2,3,6}] br[{1,2,3,7}] br[{1,2,6,7}] br[{2,3,4,5}] br[{2,3,4,6}] br[{2,3,5,6}] (br[{1,5,6,7}] br[{2,3,4,6}]-br[{1,4,6,7}] br[{2,3,5,6}]) br[{2,3,6,7}] br[{3,4,5,6}])),br[{1,2,3,4,5,6}]^4/(br[{1,2,3,4}] br[{1,2,3,6}] br[{1,2,5,6}] br[{1,4,5,6}] br[{2,3,4,5}] br[{3,4,5,6}]),br[{1,2,3,4,6,7}]^4/(br[{1,2,3,4}] br[{1,2,3,7}] br[{1,2,6,7}] br[{1,4,6,7}] br[{2,3,4,6}] br[{3,4,6,7}]),br[{1,3,4,5,6,7}]^4/(br[{1,3,4,5}] br[{1,3,4,7}] br[{1,3,6,7}] br[{1,5,6,7}] br[{3,4,5,6}] br[{4,5,6,7}])};


(* ::Section:: *)
(*Product of bosonized brackets*)


brexp[i_List]:=0/;!DuplicateFreeQ[i]
brexp[{x___,cap[i__,j__,m_],y___}]:=brexp[{x,cap[i,j,m],y}]= 
Module[{t1,t2},
t1=Sum[brexp[{x,Sequence@@(Complement[i,a]),y}]brexp[Join[a,j]]Signature[Join[Complement[i,a],a]],{a,Subsets[DeleteCases[i,Alternatives@@j],{Length[i]-m}]}];
t2=(-1)^(m+Length[{x}]Length[{y}])Sum[brexp[{x,Sequence@@(Complement[j,a]),y}]brexp[Join[a,i]]Signature[Join[Complement[j,a],a]],{a,Subsets[DeleteCases[j,Alternatives@@i],{Length[j]-m}]}];
If[Head[t1]===Times,t1,t2]
]




cbr[i_List]:=0/;!DuplicateFreeQ[i]
cbr[{x___,cap[i__,j__,m_],y___}]:=cbr[{x,cap[i,j,m],y}]= 
Module[{t1,t2},
t1=Sum[cbr[{x,Sequence@@(Complement[i,a]),y}]cbr[Join[a,j]]Signature[Join[Complement[i,a],a]],{a,Subsets[DeleteCases[i,Alternatives@@j],{Length[i]-m}]}];
t2=(-1)^(m+Length[{x}]Length[{y}])Sum[cbr[{x,Sequence@@(Complement[j,a]),y}]cbr[Join[a,i]]Signature[Join[Complement[j,a],a]],{a,Subsets[DeleteCases[j,Alternatives@@i],{Length[j]-m}]}];
If[Head[t1]===Times,t1,t2]
]

cbr[i_List]:=cbr[Sort[i]]Signature[i]/;(Sort[i]=!=i)
(*
cbr[{x___,cap[i__,j__,m_],y___}]:=cbr[{x,cap[i,j,m],y}]= Sum[cbr[{x,Sequence@@(Complement[i,a]),y}]cbr[Join[a,j]]Signature[Join[Complement[i,a],a]],{a,Subsets[DeleteCases[i,Alternatives@@j],{Length[i]-m}]}]
*)


StarProd[k_]:=k
StarProd[k___,scalar__?starProductscalarQ,y___]:=scalar StarProd[k,y]
StarProd[k___,x_Plus,y___]:=StarProd[k,#,y]&/@x
StarProd[k___,Longest[scalar__?starProductscalarQ] rest_,y___]:=scalar StarProd[k,rest,y]


$mStar=4
starProductscalarQ[expr:_[__]]:=FreeQ[expr,_?(Not@*starProductscalarQ),{1}]
starProductscalarQ[_]:=True
starProductscalarQ[a_]:=True;
starProductscalarQ[StarProd]:=False
starProductscalarQ[ br[x__?(!(Length[#]===$mStar)&)]]:=False
starProductscalarQ[ cbr[x__?(!(Length[#]===$mStar)&)]]:=False


ExpandStarAndInter[x_]:= Module[{},Block[{br=cbr,StarProd=StarProdExp},x]/.cbr-> br]

StarProdExp[k_]:=k
StarProdExp[k___,scalar__?starProductscalarQ,y___]:=scalar StarProdExp[k,y]
StarProdExp[k___,x_Plus,y___]:=StarProdExp[k,#,y]&/@x
StarProdExp[k___,x_Power?(!FreeQ[#,Plus]&),y___]:=StarProdExp[k,Expand@x,y]
StarProdExp[k___,Longest[scalar__?starProductscalarExpQ] rest_,y___]:=scalar StarProdExp[k,rest,y]
StarProdExp[k___?(FreeQ[#,StarProdExp]&&FreeQ[#,brIntersection]&&FreeQ[#,Plus]&)]:= brIntersection[k]

brIntersection[x_,y_]:=Module[{a=prodBracketsToList@x,b=prodBracketsToList@y},
1/($mStar!)Expand@Sum[Times@@(cbr[{#}]&/@Thread[cap[a,i,$mStar]]),{i,Map[b[[#]]&,Permutations[Range[$mStar]],{2}]}]
]/; (Length[prodBracketsToList@x]===$mStar)&&(Length[prodBracketsToList@y]===$mStar)

starProductscalarExpQ[expr:_[__]]:=FreeQ[expr,_?(Not@*starProductscalarExpQ),{1}]
starProductscalarExpQ[_]:=True
starProductscalarExpQ[a_]:=True;
starProductscalarExpQ[StarProd]:=False
starProductscalarExpQ[ cbr[x__?(!(Length[#]===$mStar)&)]]:=False


expandCapRule= br[{OrderlessPatternSequence[x___,cap[i__,j__,m_],y___]}]:>Sum[br[{x,Sequence@@(Complement[i,a]),y}]br[Join[a,j]]Signature[Join[Complement[i,a],a]],{a,Subsets[DeleteCases[i,Alternatives@@j],{Length[i]-m}]}];


DressNumerator[f__,i_,m_]:= DressNumerator[#,i,m]&/@f/; Head[f]===Plus
DressNumerator[f__,i_,m_]:=Module[{coef,f2},
If[FreeQ[f,br[x__]/;Length[x]>m], Return[f]];
coef=Numerator[f]/. br[x__]/;!(Length[x]==m)-> 1;
f2=coef grassTerm[Numerator[f]/coef,i]/Denominator[f];
f2=f2/. grassTerm[x__,i]:> grassTerm[ProdToList[x]/. br[a__]-> a ,i]
];

ProdRule[m_]:=br[a__]^m br[c__]^m:>( Sum[br[Drop[i,-1]]br[Prepend[c,i[[-1]]]],{i,NestList[RotateRight,a,Length[a]-1]}])^m

FormsProd[x__,y__,m_:4]:=Module[{prod},
prod=DressNumerator[Expand@(x/.br-> cbr/.cbr-> br),1,m]DressNumerator[Expand@(y/.br-> cbr/.cbr-> br),2,m]//Expand;

If[Or[FreeQ[prod, grassTerm[a__,1]], FreeQ[prod,grassTerm[a__,2]]],Return[x y]];

prod /. grassTerm[a__,1]grassTerm[b__,2]:> 1/(Length[b]!)Sum[Times@@(br[{#}]&/@Thread[cap[a,i,Length[b]]]),{i,Map[b[[#]]&,Permutations[Range[Length[b]]],{2}]}]
]



prodBracketsToList[x_]:=Block[{Times=List,Power=Table},Flatten[List@@@Flatten[x],1]]


(* ::Section:: *)
(*Graphics*)


(*  Example : Input : [1,6,4] , Output : {{"+","-","-"},{"+","+","-"}} *)
 
graphSignFlipPatterns[n_,f_,m_ : 4]:=Module[{temp},
temp=Append[#,(-1)^Boole[EvenQ[m]&&OddQ[f]]]&/@(Permutations[Join[Table[-1,{i,f}],Table[1,{i,n-m-f}]]]);
Table[Times@@Take[#,i],{i,Length[#]-1}]&/@(Prepend[#,(-1)^Boole[OddQ[m]&&OddQ[f]]]&/@temp)/. 1-> "+"/. -1-> "-"
]



cap /: MakeBoxes[cap[{i__},{j__},m_], StandardForm | TraditionalForm] := MakeBoxes[ Row[{"(",i,")",Underscript["\[Intersection]",m],"(",j ,")"}],StandardForm]
StarProd /: MakeBoxes[StarProd[i_,j_], StandardForm | TraditionalForm] := MakeBoxes[ Row[{"(",i,")""**","(",j ,")"}],StandardForm]
(*Global`cc /; MakeBoxes[Global`cc[a__], StandardForm | TraditionalForm] :=MakeBoxes[SubscriptBox[Global`cc,a] ,StandardForm]*)


bello[exprn_]:=Block[{
integerPaddingRule={(integerSequence:_Integer..)/;(Length[{integerSequence}]>1):>(integerSequence/.{q_Integer:>If[q>9,Row[List[Spacer[2],ToString[q],Spacer[2]]],ToString[q]]})},
capRule={cap[{x__},{y__},m_]:>Row[{"(",x,")","\[Intersection]","(",y,")"}]},
subscriptRule={head_[q__]/;And@@IntegerQ/@{q}&&!head===List  :> Subscript[head,q]},
ruleRule=({ruleList:{_Rule..}:>Block[{ruleRows=({ruleList/. {(q_->r_):>Row[{q,"\[Rule]",r},Alignment->Center]}})},(Grid[((#)/.({}->"")),ItemStyle->{FontSize->1.4($DefaultFont)[[2]]},ItemSize->Full,Alignment->Left])&@Transpose@Partition[Flatten[ruleRows,1],Ceiling[Length[Flatten[ruleRows,1]]/Which[Length[Flatten[ruleRows,1]]<10,1,Length[Flatten[ruleRows,1]]<20,2,True,3]],Ceiling[Length[Flatten[ruleRows,1]]/Which[Length[Flatten[ruleRows,1]]<10,1,Length[Flatten[ruleRows,1]]<20,2,True,3]],1,{{}}]]}),
matrixRule={Grid[q_?MatrixQ,y___]:>Grid[q,y],q_?MatrixQ:>MatrixForm[q]}},Fold[Replace[#1,#2,{0,\[Infinity]}]&,exprn,{integerPaddingRule,capRule,subscriptRule,ruleRule}]/.matrixRule]


(* ::Section:: *)
(*End of context*)


Print["===============AmplituhedronLikeG================"];
Print["Author: Gabriele Dian (Durham University)"];
Print["Please report any bug to:"];
Print["gabriele.dian@durham.ac.uk"];
Print["Version 1.0 , last update 26/01/2021"];
Print[Hyperlink["Click here for full documentation","https://google.com"]];
Print["============================================="];


(*End the private context*)
End[]

(*Protect all public symbols in the package*)
Protect@@Names["AmplituhedronLG`*"];
Unprotect[AmplituhedronLG`cbr,AmplituhedronLG`mStar];

(*End the package*)
EndPackage[]
