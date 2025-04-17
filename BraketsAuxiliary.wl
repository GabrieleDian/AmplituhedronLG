(* ::Package:: *)

(* ::Chapter:: *)
(*Brakets Auxiliary *)


BeginPackage["BraketsAuxiliary`"]


(*In order to allow the package to be reloaded we unprotect and clear all the symbol definitions*)
Unprotect@@Names["BraketsAuxiliary`*"];
ClearAll@@Names["BraketsAuxiliary`*"];


(* ::Section::Closed:: *)
(*Functions Description*)


(* ::Subsection::Closed:: *)
(*Twistor Brakets*)


x::usage=" x[i,j] is an ordered symmetric function representing a contraction of two twistors."
xTobrRule::usage="xTobrRule[exp,n], where n is the number of particels, transforms x[i,j] to br[{i-1,i,j-1,j}] for j>n, br[{i-1,i,A[j],B[j]}] and for i>n to br[{A[i],B[i],A[j],B[j]}]."


(* ::Subsection::Closed:: *)
(*Momentum Twistor Brakets*)


br::usage=" br[Z] takes List as a input is a ordered anti-symmetric multilinear function. Which variables are scalar is controlled by the function scalarQ."
scalarQ::usage="scalarQ controlles the linearity properties of br."
A::usage="A[i] is a loop variable."
B::usage="B[i] is a loop variable."


(* ::Subsection::Closed:: *)
(*Auxiliary Functions*)


ProdToList::usage=" ProdToList is a listable function that changes Times with List and Power with Table."
SumToList::usage="SumToList[a] replace the Head of x with List if Head[a]===Plus."
removeCoefficientX::usage="removeCoefficientX[a] Removes all coefficents in x in the polynomial a."


(* ::Section::Closed:: *)
(*Private context starts here*)


Begin["`Private`"]


(* ::Section:: *)
(*Twistor Brakets*)


x[i_,j_]:= x[j,i]/; i>j


xTobrRule[n_]:={x[i_,j_]/;j<= n:> br[{Mod[i-1,n,1],i,Mod[j-1,n,1],j}],x[i_,j_]/;i<= n:> br[{Mod[i-1,n,1],i,A[j],B[j]}], x[i_,j_]:> br[{A[i],B[i],A[j],B[j]}]};


(* ::Subsection:: *)
(*Visualization*)


xBracketBox[a_, b_] :=
    TemplateBox[{a, b}, "xBox",
        DisplayFunction -> (SubscriptBox["x", RowBox[{#1,",",#2}]]&),
        InterpretationFunction -> (RowBox[{"x","[",RowBox[{#1,",",#2}],"]"}]&)]


x /: MakeBoxes[x[a_, b_], StandardForm | TraditionalForm] := xBracketBox[ToBoxes[a], ToBoxes[b]];


(* ::Section::Closed:: *)
(*Momentum Twistor Brakets*)


br[i_List]:=br[Sort[i]]Signature[i]/;(Sort[i]=!=i)
br[i_List]:=0/;!DuplicateFreeQ[i]
br[{b___,x_Plus,y___}]:=br[{b,#,y}]&/@x
br[{k___,Longest[scalar__?scalarQ] rest__,y___}]:=scalar br[{k,rest,y}]


scalarQ[expr:_[__]]:=FreeQ[expr,_?(Not@*scalarQ),{1}]
scalarQ[_]:=True
scalarQ[a_]:=NumberQ[a];
scalarQ[br[__]]:=True
scalarQ[A]=False;
scalarQ[B]=False;
scalarQ[z]=False;


(* ::Subsection:: *)
(*Visualization*)


(*br visualization*)


brBox[a_,b__] := 
 TemplateBox[{a,b}, "br", 
  DisplayFunction -> (  TemplateBox[{"\[LeftAngleBracket]",b,"\[RightAngleBracket]"},"RowDefault"] &), 
  InterpretationFunction ->(RowBox[{"br","[",a,"]"}]&)]


br /: MakeBoxes[br[xx_], StandardForm | TraditionalForm] := brBox[ToBoxes@xx,Sequence@@ToBoxes/@xx]


(*A visualization*)


ABox[a_] :=
    TemplateBox[{a}, "ABox",
        DisplayFunction -> (SubscriptBox["A", RowBox[{#1}]]&),
        InterpretationFunction -> (RowBox[{"A","[",RowBox[{#1}],"]"}]&)]


A /: MakeBoxes[A[a_], StandardForm | TraditionalForm] := ABox[ToBoxes[a]];


(*B visualization*)


BBox[a_] :=
    TemplateBox[{a}, "BBox",
        DisplayFunction -> (SubscriptBox["B", RowBox[{#1}]]&),
        InterpretationFunction -> (RowBox[{"B","[",RowBox[{#1}],"]"}]&)]


B /: MakeBoxes[B[a_], StandardForm | TraditionalForm] := BBox[ToBoxes[a]];


(*Shortcut definition*)
(*If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "br" -> brbox[{\[Placeholder],\[Placeholder]}]]];
    ];*)
  
    


(* ::Section::Closed:: *)
(*Auxiliary Functions*)


(*removeCoefficientX[3x[1,2]+2x[3,4]] Out: Subscript[x, 1,2]+Subscript[x, 3,4]*)
SetAttributes[removeCoefficientX,Listable]
removeCoefficientX[k_Plus]:=removeCoefficientX/@k
removeCoefficientX[0]=0;
removeCoefficientX[k_]:= k/(k/.x[__]->1)


Attributes[SumToList]=Listable;
SumToList[f_] /; Head[f] === Plus :=List@@f
SumToList[f_] :={f}


SetAttributes[ProdToList,Listable]
ProdToList[x_]:=Block[{Times=List,Power=Table},If[Head[x]===List,Flatten@x,{x}]]


(* ::Section:: *)
(*End Context*)


Print["===============Brakets Auxiliary================"];
Print["============================================="];


(*End the private context*)
End[]

(*Protect all public symbols in the package*)
Protect@@Names["BraketsAuxiliary`*"];
Unprotect[BraketsAuxiliary`scalarQ];

(*End the package*)
EndPackage[]
