/*
Copyright 2018 Bjoern Lellmann

    This file is part of nnProver.

    nnProver is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    nnProver is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with nnProver.  If not, see <http://www.gnu.org/licenses/>.
*/

/* Usage:
   Formulae are built from the grammar

     Phi ::= atom | false | true | neg Phi | Phi and Phi | Phi or Phi | Phi -> Phi | ea Phi | aa Phi

   where atom is any Prolog atom, e.g., p,q,r,...,a1,a2,a3,... 
   The usual conventions about binding strength of the connectives apply, i.e.,
   the unary connetives bind stronger than the binary ones, 'and'
   binds stronger than 'or' binds stronger than '->'.

   Run the prover with the command

     ?- prv( Formula, Axioms).

   where formula, e.g., p -> q or s, and Axioms is a list of
   additional axioms. So far these are:

    - nea: neg ea false (equivalent to dea: neg(ea p and aa neg p))
    - dae: aa p -> ea p
    - daa: neg(aa p and aa neg p)

   To see the output as a pdf, run latex or pdflatex on the file output.tex 
   and view the resulting file in your favorite viewer (you might need to zoom
   in quite a bit for large derivations).
   NOTE: In some cases the derivations might become too large for TeX to handle
      (if they are more than about 19 feet). In this case you might need to
      split the derivation produced in derivation.tex manually.
*/


/* operator definitions etc */
  :- op(400,fy,[neg,ea,aa]),
     op(500,xfy,and),
     op(600,xfy,or),
     op(700,xfy,->),
     op(800,xfx,=>).

  :- use_module(library(lists)).


/* sequents are tuples (Gamma => Delta) with Gamma,Delta lists of
 * formulae.  nested sequents are labelled trees ns(Seq,Label,Suc)
 * where every node is decorated with a sequent Seq and a label Label
 * and has a list Suc of nested sequents as successors.  Further we
 * have "unfinished" sequents nsunf(Seq,[]) and "finished" sequents
 * nsfin(Seq,[]), where Seq is a sequent each.
*/


/* ns /1 */
/* Test whether something is a nested sequent */
ns((_ => _),_,List) :- nslist(List).
ns(nsunf((_ => _),[])).
ns(nsfin((_ => _),[])).
nslist([]).
nslist([Ns|Tail]) :- ns(Ns), nslist(Tail).


/* PICK NS 3 */
/* pick ns(NS1,NS2,NS3) */
/* picks a subtree NS1 of a nested sequent NS2 and replaces it with a
 * hole, resulting in NS3 */
pick_ns(NS,NS,hole).
pick_ns(NS,ns(Seq,Lbl,Suc1),ns(Seq,Lbl,Suc2)) :-
    select(NS1,Suc1,NS2,Suc2),
    pick_ns(NS,NS1,NS2).


/* prv /2 */ 
/* prv((Gamma => Delta),Axioms) checks whether the sequent (Gamma => Delta)
 * is derivable using the axioms Axioms, displays the result and writes the
 * derivation resp. countermodel into the file derivation.tex
*/
prv(Fml,Axioms) :- prv_with_filename([] => [Fml],Axioms,'output.tex').


/* prv_online /4 */
/* Used in the online system on the website. Takes a formula, the code
 * for the axioms, and the name of an output file, and calls
 * prv_with_filename.
*/
prv_online(Fml,Axioms,Filename) :-
    prv_with_filename( [] => [Fml], Axioms, Filename),!.


/* prv_with_filename /3 */
/* Takes a standard sequent, a list of axioms, and a filename, tries to prove
 * the sequent in the logic with the axioms using predicate provable, prints the
 * result on the screen, and writes it to the specified file.
*/

prv_with_filename((Gamma => Delta),Axioms,Filename) :-
    open(Filename,write,Stream1),
    write(Stream1,'\\documentclass{article}'),nl(Stream1),
    write(Stream1,'\\usepackage{header}'),nl(Stream1),
    write(Stream1,'\\begin{document}'),nl(Stream1),
    close(Stream1),!,
    provable(ns((Gamma => Delta),[],[]),Tree,Result,CountermodelOut,Axioms),
    ns2model(CountermodelOut,Axioms,Countermodel),
    printDerMod((Gamma => Delta),Tree,Result,Countermodel),!,
    open(Filename,append,Stream),
    write(Stream,'\\begin{center}'),nl(Stream),
    write(Stream,'Additional axioms: '),
    write(Stream,'Input sequent: '),nl(Stream),
    write(Stream,'$'),ppwriteFList(Stream,Gamma),
    write(Stream,' \\seq '),
    ppwriteFList(Stream,Delta),write(Stream,'$'),nl(Stream),
    nl(Stream),
    pprintresult(Stream,Tree,Result,Countermodel),
    write(Stream,'\\end{center}'),nl(Stream),
    write(Stream,'\\end{document}'),
    close(Stream),!.


/* printDerMod /4 */
/* prints the result to screen */
printDerMod(_,_,failed,Countermodel) :-
    nl, print('Countermodel found!'),nl,nl,
    ppModel(Countermodel),nl.
printDerMod(_,Tree,succeeded,_) :-
    nl, print('Derivation found!'),nl,
    pptree(Tree),nl.


/* pprintresult /4 */
/* prints result to Stream */
pprintresult(Stream,Tree,succeeded,_) :-
    write(Stream,'Derivation found!'),nl(Stream),
    ppwrite(Stream,Tree).
pprintresult(Stream,_,failed,Countermodel) :-
    write(Stream,'Countermodel found!'),nl(Stream),
    ppwriteModelNew(Stream,Countermodel).


/* countermodelchoice /6 */
/* for two-premiss rules: if proof search for either of the premisses
 * failed, then proof search of the conclusion fails. The countermodel
 * is passed on.
*/
countermodelchoice(failed,Model,_,_,failed,Model).
countermodelchoice(succeeded,_,failed,Model,failed,Model).
countermodelchoice(succeeded,Model,succeeded,_,succeeded,Model).
    

/* provable /4 */
/* checks whether NS is derivable using Axioms and outputs the derivation
 * tree (if exists), the result, and the countermodel (if exists).
*/
/* NOTE: we use invisible formulae inv(A) for loop
 * checking.
*/

/* initials */
provable(NS,init(NS),succeeded,noModel,_) :-
    pick_ns(ns((Gamma => Delta),_,_), NS, _),
    member(F, Gamma),
    member(F, Delta).
provable(NS,botL(NS),succeeded,noModel,_) :-
    pick_ns(ns((Gamma => _),_,_), NS, _),
    member(false, Gamma).
provable(NS,topR(NS),succeeded,noModel,_) :-
    pick_ns(ns((_ => Delta),_,_), NS, _),
    member(true, Delta).

/* negation left */
provable(NS,negL(NS,[Tree]),Result,Model,Axioms) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    select(neg F, Gamma, Sigma), 
    \+ member(inv(F), Delta), % loop check: formula not yet there
    \+ member(F, Delta),
    pick_ns(ns(([inv(neg F)|Sigma] => [F|Delta]),Lbl,Suc),NewNS, NsHole),
    provable(NewNS,Tree,Result,Model,Axioms).

/* negation right */
provable(NS,negL(NS,[Tree]),Result,Model,Axioms) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    select(neg F, Delta, Pi), 
    \+ member(inv(F), Gamma), % loop check: formula not yet there
    \+ member(F, Gamma),
    pick_ns(ns(([F|Gamma] => [inv(neg F)|Pi]),Lbl,Suc),NewNS, NsHole),
    provable(NewNS,Tree,Result,Model,Axioms).

/* conjunction left */
provable(NS,andL(NS,[Tree]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    select(F and G, Gamma, Sigma), 
    (\+ member(inv(F), Gamma), % loop check: at least on conjunct not there
    \+ member(F, Gamma)
      ;
    \+ member(inv(G), Gamma),
    \+ member(G, Gamma)),
    pick_ns(ns(([F,G,inv(F and G)|Sigma] => Delta),Lbl,Suc),NewNS, NsHole),
    provable(NewNS,Tree,Result,Model,Logic).

/* disjunction right */
provable(NS,orR(NS,[Tree]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    select(F or G, Delta, Pi), 
    (\+ member(inv(F), Delta), % loop check: at least one disjunct not there
    \+ member(F, Delta)
      ;
    \+ member(inv(G), Delta),
    \+ member(G, Delta)),
    pick_ns(ns((Gamma => [F,G,inv(F or G)|Pi]),Lbl,Suc),NewNS, NsHole),
    provable(NewNS,Tree,Result,Model,Logic).

/* implication right */
provable(NS,impR(NS,[Tree]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member( F -> G, Delta),
    (\+ member(F,Gamma), % loop check: at least one of the formulae is
                         % not there
    \+ member(inv(F),Gamma)
     ;
    \+ member(G,Delta),
    \+ member(inv(G),Delta)),
    select(F->G, Delta,Pi), 
    pick_ns(ns(([F|Gamma] => [G,inv(F -> G)|Pi]),Lbl,Suc),NewNS, NsHole),
    provable(NewNS,Tree,Result,Model,Logic).

/* local modal rules */
/* aa left */
provable(NS,aaL(NS,[Tree]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl1,Suc), NS, NsHole),
    member( aa(A), Gamma),
    select( ns((Sigma => Pi),Lbl2,SucSuc), Suc, Suc2),
    \+ member(A,Sigma),
    \+ member(inv(A),Sigma),
    pick_ns(ns((Gamma => Delta),Lbl1,[ns(([A|Sigma] => Pi),Lbl2,SucSuc)|Suc2]),NewNS,
	    NsHole),
    provable(NewNS,Tree,Result,Model,Logic).
	 
/* ea right */
provable(NS,eaR(NS,[Tree]),Result,Model,Axioms) :-
    pick_ns(ns((Gamma => Delta), Lbl, Suc), NS, NsHole),
    member( ea(A), Delta),
    \+ member(nesunf([]=>[A],[]),Delta),
    pick_ns(ns((Gamma => [nesunf([] => [A],[])|Delta]), Lbl, Suc), NewNS,
	    NsHole),
    provable(NewNS,Tree,Result,Model,Axioms).

/* ea left */
provable(NS,eaL(NS,[Tree]),Result,Model,Axioms) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member( ea(A), Gamma),
    member( nesunf((Sigma => Pi),[]), Delta),
    \+ containedNesIn(nesfin([A|Sigma] => Pi,[]),Delta),
    pick_ns(ns((Gamma => [nesfin([A|Sigma] => Pi, [])|Delta]),Lbl,Suc),NewNS,
	    NsHole),
    provable(NewNS,Tree,Result,Model,Axioms).
	 
/* Extension: eaN */
/* for the axiom aeD: aa a -> ea A */
/* also used for the axiom aaD: neg (aa a and aa neg a) */
provable(NS,eaN(NS,[Tree]),Result,Model,Axioms) :-
    (member(aeD,Axioms)
     ;
     member(aaD,Axioms)),
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member( nesunf((Sigma => Pi),[]), Delta),
    \+ containedNesIn(nesfin(Sigma => Pi,[]),Delta),
    pick_ns(ns((Gamma => [nesfin(Sigma => Pi, [])|Delta]),Lbl,Suc),NewNS,
	    NsHole),
    provable(NewNS,Tree,Result,Model,Axioms).

/* W-rule */
provable(NS,aaea(NS,[Tree]),Result,Model,Axioms) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member( aa(_), Delta),
    member( nesunf((Sigma => Pi),[]), Delta),
    \+ containedNesIn(nesfin(Sigma => Pi,[]),Delta),
    pick_ns(ns((Gamma => [nesfin(Sigma => Pi, [])|Delta]),Lbl,Suc),NewNS,
	    NsHole),
    provable(NewNS,Tree,Result,Model,Axioms).

/* two-premiss rules */
/* conjunction right*/
provable(NS,andR(NS,[Tree1,Tree2]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    select(F and G, Delta, Pi), 
    \+ member(inv(F), Delta), % loop check: none of the conjuncts is there
    \+ member(F, Delta),
    \+ member(inv(G), Delta),
    \+ member(G, Delta),
    pick_ns(ns((Gamma => [F,inv(F and G)|Pi]),Lbl,Suc),NewNS1, NsHole),
    pick_ns(ns((Gamma => [G,inv(F and G)|Pi]),Lbl,Suc),NewNS2, NsHole),
    provableList(succeeded,[NewNS1,NewNS2],[Tree1,Tree2],Result,Model,
		 Logic).

/* disjunction left*/
provable(NS,orL(NS,[Tree1,Tree2]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    select(F or G, Gamma, Sigma), 
    \+ member(inv(F), Gamma), % loop check: none of the disjuncts is there
    \+ member(F, Gamma),
    \+ member(inv(G), Gamma),
    \+ member(G, Gamma),
    pick_ns(ns(([F,inv(F or G)|Sigma] => Delta),Lbl,Suc),NewNS1, NsHole),
    pick_ns(ns(([G,inv(F or G)|Sigma] => Delta),Lbl,Suc),NewNS2, NsHole),
    provableList(succeeded,[NewNS1,NewNS2],[Tree1,Tree2],Result,Model,
		 Logic).

/* implication left*/
provable(NS,impL(NS,[Tree1,Tree2]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member( F -> G, Gamma),
    \+ member(F,Delta), % loop check: none of the formulae is there
    \+ member(inv(F),Delta),
    \+ member(G,Gamma),
    \+ member(inv(G),Gamma),
    select(F->G, Gamma,Sigma),
    pick_ns(ns(([G,inv(F -> G)|Sigma] => Delta),Lbl,Suc),NewNS1, NsHole),
    pick_ns(ns((Gamma => [F|Delta]),Lbl,Suc),NewNS2, NsHole),
    provableList(succeeded,[NewNS1,NewNS2],[Tree1,Tree2],Result,Model,
		 Logic).

/* non-local modal rules */
/* aa right */
provable(NS,aaR(NS,[Tree]),Result,Model,Logic) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member( aa(A), Delta),
    \+ occursIn( A, Suc),
    pick_ns(ns((Gamma => Delta),Lbl,[ns(([] => [A]),[],[])|Suc]),NewNS,
	    NsHole),
    provable(NewNS,Tree,Result,Model,Logic).
	 
/* jump */
provable(NS,jump(NS,[Tree]), Result, Model, Axioms) :-
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    member(nesfin(Sigma => Pi, []), Delta),
    \+ containedNesIn(Sigma => Pi, Suc),
    pick_ns(ns((Gamma => Delta), Lbl, [ns(Sigma => Pi,Sigma, [])|Suc]), NewNS,
	    NsHole),
    provable(NewNS, Tree, Result, Model, Axioms).

/* Extension: P rule for ea */
/* for the axiom eaN: neg ea false */
provable(NS,eaP(NS,[Tree]), Result, Model, Axioms) :-
    member(eaN,Axioms),
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    \+ containedNesIn(nesunf([]=>[],_), Delta),
    (member(_,Gamma) % NOTE: this is purely against loops together
                     % with axiom aaD!
    ;
    member(_,Delta)),
    pick_ns(ns((Gamma => [nesunf([]=>[],[])|Delta]), Lbl, Suc), NewNS,
	    NsHole),
    provable(NewNS, Tree, Result, Model, Axioms).

/* Extension: D rule for aa */
/* for the axiom aaD: neg (aa a and aa neg a) */
provable(NS,aaD(NS,[Tree]), Result, Model, Axioms) :-
    member(aaD,Axioms),
    pick_ns(ns((Gamma => Delta),Lbl,Suc), NS, NsHole),
    (\+ Gamma = [] ; \+ Delta = []), % Loop check: don't apply twice.
    \+ containedNesIn([]=>[], Suc),
    pick_ns(ns((Gamma => Delta), Lbl, [ns([] => [],[],[])|Suc]), NewNS,
	    NsHole),
    provable(NewNS, Tree, Result, Model, Axioms).


/* for countermodel construction: We use that all the rules are
 * invertible and return the current nested sequent at this point:
 * since all the rules are invertible, once none of the clauses can be
 * applied, the sequent is not provable (since there are no bad
 * choices in the proof search).
*/

provable(Ns,failed,failed,Ns,_).


/* occursIn /2
   For checking whether an implication or its invisible form occurs in the
   RHS of the successors of a node.
*/
occursIn(F,[ns((_ => Delta),_, _) |Tail]) :-
    member(F,Delta) ; member(inv(F),Delta) ; occursIn(F,Tail).


/* containedIn /2
 * For checking whether a sequent is in weakened form contained in a
 * list of nested sequents.
*/
containedIn(Gamma => Delta, [ns(Sigma => Pi,_, _)|_]) :-
    subset(Gamma,Sigma),
    subset(Delta,Pi).
containedIn(Gamma => Delta, [_|Suc]) :-
    containedIn(Gamma => Delta, Suc).


/* containedNesIn /2
 * For checking whether a finished or unfinished sequent in weakened
 * form is contained in the RHS of a sequent.
*/
containedNesIn(nesfin(Gamma => Delta,[]), [nesfin(Sigma => Pi,_)|_]) :-
    addInv(Sigma,Sigma2),
    subset(Gamma,Sigma2),
    addInv(Pi,Pi2),
    subset(Delta,Pi2).
containedNesIn(nesunf(Gamma => Delta,[]), [nesunf(Sigma => Pi,_)|_]) :-
    addInv(Sigma,Sigma2),
    subset(Gamma,Sigma2),
    addInv(Pi,Pi2),
    subset(Delta,Pi2).
containedNesIn(Gamma => Delta, [ns(Sigma => Pi,_, _)|_]) :-
    addInv(Sigma,Sigma2),
    subset(Gamma,Sigma2),
    addInv(Pi,Pi2),
    subset(Delta,Pi2),!.
containedNesIn(Seq,[_|Tail]) :-
    containedNesIn(Seq,Tail).


/* addInv /2
 * adds all the visible versions of invisible formulae.
*/
/* NOTE: Currently doesn't have any effect to prevent the bloating of
 * sequents.
*/
addInv([],[]).
addInv([inv(A)|Tail1],[A,inv(A)|Tail2]) :-
    addInv(Tail1,Tail2).
addInv([A|Tail1],[A|Tail2]) :-
    addInv(Tail1,Tail2).


/* provableList /5 */
/* provableList(Logic,NSList,TreeList,Result,Model) checks that all
 * nested sequents in NSList are derivable in Logic
 * and gives the list TreeList of their derivation trees, the Result,
 * and the possible countermodel Model.
*/
provableList(failed,_,_,failed,ns(([] => [d,u,m,m,y]),[],[]),_).
provableList(succeeded,[NS],[Tree],Result,Model,Logic) :-
    provable(NS,Tree,Result,Model,Logic).
provableList(succeeded,[NS|Tail],[Tree|TreeTail],Result,Model,Logic) :-
    provable(NS,Tree,NsResult,NsModel,Logic),
    provableList(NsResult,Tail,TreeTail,ListResult,ListModel,Logic),
    countermodelchoice(NsResult,NsModel,ListResult,ListModel,Result,
		       Model).
/* note that countermodelchoice gives the first countermodel, so the
 * initialisation in the provableList(failed,...) clause does not
 * mess up things.
*/



/*******************/
/* pretty printing */
/*******************/

/* pptree /1 */
/* print derivation trees */
pptree(Term) :-
	pptreeAux(Term,0).

pptreeAux(Term,Nest) :-
	Term =.. [Op|[NS]],
	Op == init,
	nl, tab(Nest+2), write(Op), write('('),
	ppNSeq(NS),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[NS]],
	Op == botL,
	nl, tab(Nest+2), write(Op), write('('),
	ppNSeq(NS),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[NS]],
	Op == topR,
	nl, tab(Nest+2), write(Op), write('('),
	ppNSeq(NS),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[NS|[List]]],
	Op \== =>,
	nl, tab(Nest+2), write(Op), write('('),
	ppNSeq(NS),
	pptreeList(List,Nest+2),
	nl, tab(Nest+3),write(')').


/* pptreeList
   pretty print a list of derivation trees
*/
pptreeList([],_).
pptreeList([H|Tl],Nest) :-
	pptreeAux(H,Nest),
	pptreeList(Tl,Nest).


/* ppNSeq /1 */
/* pretty print nested sequents */
ppNSeq(ns((Gamma => Delta),Lbl,Suc)) :-
    write('(label: '),
    ppFList(Lbl),
    write(') '),
    ppSeq((Gamma => Delta)),
    ppNSeqList(Suc),!.

/* ppNSeqList
   pretty print a list of nested sequents
*/
ppNSeqList([]).
ppNSeqList([Ns|Tail]) :-
    write(' [ '),
    ppNSeq(Ns),
    write(' ] '),
    ppNSeqList(Tail),!.


/* ppSeq /1 */
/* print sequents */
ppSeq((Gamma => Delta)) :-
    strip_invisible(Gamma,Sigma),
    strip_invisible(Delta,Pi),
    ppFList(Sigma),write(' => '),ppFList(Pi).


/* ppFList /1 */
/* print list of formulae omitting invisible formulae */
ppFList([]).
ppFList([inv(_)|Tail]) :- ppFList(Tail).
ppFList(nesfin(Seq,[])) :- 
    write('nesfin('),
    ppSeq(Seq),
    write(')').
ppFList(nesunf(Seq,[])) :- 
    write('nesfin('),
    ppSeq(Seq),
    write(')').
ppFList([F|[]]) :- write(F).
ppFList([F,G|Tail]) :- write(F), write(', '),ppFList([G|Tail]),!.


/* ns2model /3:
 * turns a nested sequent into a description of a model.
 * A model is given as a tree
 * depends on the axioms given
*/
ns2model(noModel,_,noModel).
ns2model(ns(Seq,Lbl,Suc), Axioms,Model) :-
    ns2modelAux([ns(Seq,Lbl,Suc)], [0], Axioms, [Model]).


/* ns2modelAux:
 * takes list of nested sequents (aka successors), the current name
 * (aka list of naturals), the list of axioms, and creates list of models.
*/
ns2modelAux([],_,_,[]).
/*ns2modelAux([ns(Gamma => Delta, Lbl, [])|Tail], CurrentNamePredecName, CurrentIndex,
	    , mod(Name,Lbl, Gamma => Delta, Nbh, []) .*/
ns2modelAux([ns(Seq,Lbl,Suc)|TailSeq],[N|TailName], Axioms
	    , [mod([NewName|TailName],Lbl,Seq,Nbh,SucModels)|TailModel]) :-
    NewName is N+1,
    ns2modelAux(Suc,[0,NewName|TailName],Axioms,SucModels),
    computeNeighbourhood(Seq,SucModels,Axioms,Nbh),
    ns2modelAux(TailSeq,[NewName|TailName],Axioms,TailModel).


/* computeNeighbourhood:*/
/* takes the sequent, the list of successors (as models) and the list
 * of axioms, and gives
 * a list of neighbourhoods.
*/
computeNeighbourhood(_ => Delta ,[],_,[]) :-
    member(ea(_),Delta),!.
computeNeighbourhood(Seq,[],Axioms,Nbh) :-
    modify_for_axioms(Seq,[empty],Axioms,Nbh),!.
computeNeighbourhood(Gamma => Delta,ModList,Axioms,Nbh_out) :-
    setof(Name,Label^Seq^Nbh^SucModels^
	       member(mod(Name,Label,Seq,Nbh,SucModels),ModList),
	  Namelist), % collect list of all successors
    setof(Label,Name^Seq^Nbh^SucModels^
		member(mod(Name,Label,Seq,Nbh,SucModels),ModList),
	  Labellist), % collect list of all labels
    maplist(computeForLabel(ModList),Labellist,Nbh1), % create list of
                                                      % "proper" neighbourhoods
    (member(ea(_),Delta),
     list_to_set([Namelist|Nbh1],Nbh2),
     subtract(Nbh2,[empty],Nbh),!
     ;
     append([empty,Namelist],Nbh1,Nbh2),
     list_to_set(Nbh2,Nbh)),
    modify_for_axioms(Gamma => Delta, Nbh,Axioms,Nbh_out).

computeForLabel(ModList,Label,Set) :-
    findall(Name,member(mod(Name,Label,_,_,_),ModList),Set).


/* modify_for_axioms
   for modifying the constructed neighbourhoods according to the
   additional axioms.
*/
modify_for_axioms(_,Nbh,[],Nbh).
% for axiom eaN: remove the emptyset everywhere
modify_for_axioms(Gamma => Delta,Nbh_in,Axioms,Nbh_out) :-
    member(eaN,Axioms),
    subtract(Nbh_in,[empty],Nbh),
    subtract(Axioms,[eaN],Axioms2),
    modify_for_axioms(Gamma => Delta,Nbh,Axioms2,Nbh_out).
% for axiom aeD: nothing to modify
% NOTE: this doesn't seem to work modularly for the combination
% with axiom eaN: that one kicks out the emptyset, but that might make
% the set of neighbourhoods empty. Shouldn't matter as long as we have
% only the combination with aaD, though...
modify_for_axioms(Seq,Nbh_in,Axioms,Nbh_out) :-
    member(aeD,Axioms),
    subtract(Axioms,[aeD],Axioms2),
    modify_for_axioms(Seq,Nbh_in,Axioms2,Nbh_out).
% for axiom aaD: if sequent is empty, replace with only [self]
modify_for_axioms([] => [],_,Axioms,[self]) :-
    member(aaD,Axioms).
modify_for_axioms(Gamma => Delta,Nbh_in,Axioms,Nbh_out) :-
    member(aaD,Axioms),
    (member(_,Gamma)
    ;
    member(_,Delta)),
    subtract(Axioms,[aaD],Axioms2),
    modify_for_axioms(Gamma => Delta,Nbh_in,Axioms2,Nbh_out).
    

/* ppModel /1 */
/* prints a model */
ppModel(Model) :-
    ppModelAux(Model,0).

ppModelAux(mod(Name,Lbl,Gamma => Delta,Nbh,[]),N) :-
    list_to_set(Gamma,Sigma),
    strip_invisible(Sigma,Omega),
    tab(N),
    ppWorld(Name),
    write(': Label: '),
    write(Lbl),
    nl,tab(N+4),
    write('True formulae: '),
    write(Omega),
    list_to_set(Delta,Pi),
    strip_nonformulae(Pi,Theta),
    nl,tab(N+4),
    write('False formulae: '),
    write(Theta),
    nl,
    tab(N+4),
    write('Neighbourhoods: '),
    (Nbh = [],
     write('emptyset')
     ;
     Nbh = [ self ], % This is the case for axiom aaD: reflexive world
     write(' { { '),
     ppWorld(Name),
     write(' } } ')
     ;
     \+ Nbh = [],
     \+ Nbh = [ self ],
     write('{ '),
    ppNbh(Nbh),
    write(' }')).
ppModelAux(mod(Name,Lbl,Gamma => Delta,Nbh,ModList),N) :-
    list_to_set(Gamma,Sigma),
    strip_invisible(Sigma,Omega),
    tab(N),
    ppWorld(Name),
    write(': Label: '),
    write(Lbl),
    nl,tab(N+4),
    write('True formulae: '),
    write(Omega),
    list_to_set(Delta,Pi),
    strip_nonformulae(Pi,Theta),
    nl,tab(N+4),
    write('False formulae: '),
    write(Theta),
    nl,
    tab(N+4),
    write('Neighbourhoods: '),
    (Nbh = [],
     write('emptyset')
     ;
     \+ Nbh = [],
     write('{ '),
    ppNbh(Nbh),
    write(' }')),
    nl,nl,
    ppModelList(ModList,N+4).


/* ppModelList
   for pretty printing a list of models
*/
ppModelList([Model|[]],N) :-
    ppModelAux(Model,N).
ppModelList([Model|Tail],N):-
    ppModelAux(Model,N),
    nl, tab(N),
    nl,
    ppModelList(Tail,N),
    nl.


ppNbh([]). 
ppNbh([Set|[]]) :-
    (Set = empty,
     write(' emptyset ')
     ;
     Set = self,
     write(' {self} ') 
     ;
     \+ Set = empty,
    write(' { '),
    ppSet(Set),
    write(' } ')).
ppNbh([Set1,Set2|Tail]) :-
    (Set1 = empty,
     write(' emptyset, ')
     ;
     \+ Set1 = empty,
    write(' { '),
    ppSet(Set1),
    write(' }, ')),
    ppNbh([Set2|Tail]).


ppSet([]).
ppSet([Name|[]]) :-
    ppWorld(Name).
ppSet([Name1,Name2|Tail]) :-
    ppWorld(Name1),
    write(', '),
    ppSet([Name2|Tail]).


/* OLD ONE: */
ppModelOld(Ns) :-
    ppModel2(Ns,0).

ppModel2(ns((Gamma => _),_,[]),N) :-
    list_to_set(Gamma,Sigma),
    strip_invisible(Sigma,Omega),
    tab(N),
    write(Omega).
ppModel2(ns((Gamma => _),_,Suc),N) :-
    list_to_set(Gamma,Sigma),
    strip_invisible(Sigma,Omega),
    tab(N),
    write(Omega),
    write(' < '),
    nl,
    ppModelListOld(Suc,N+4).

ppModelListOld([Ns|[]],N) :-
    ppModel2(Ns,N).
ppModelListOld([Ns|Tail],N):-
    ppModel2(Ns,N),
    nl, tab(N),
    nl,
    ppModelListOld(Tail,N),
    nl.


/* ppWorld /1
 * pretty print a world: reverse the list and make it look nice
*/
ppWorld(World) :-
    reverse(World,Dlorw),
    ppWorldAux(Dlorw).
ppWorldAux([]).
ppWorldAux([N|[]]) :-
    write(N),!.
ppWorldAux([N,M|Tail]) :-
    write(N),write('.'),
    ppWorldAux([M|Tail]),!.
/* END OF MODEL PRINTING */

    
/* For writing LaTeX into the output file: */

/* ppwrite /2 takes the stream and the proof tree */
ppwrite(Stream,Tree) :-
    nl(Stream),write(Stream,'\\['),nl(Stream),
    write(Stream,'\\begin{adjustbox}{max width=\\textwidth}'),nl(Stream),
    ppwriteAux(Stream,Tree,0),
    nl(Stream),write(Stream,'\\end{adjustbox}'),
    nl(Stream),write(Stream,'\\]'),nl(Stream),nl(Stream),!.


/* ppwriteAux /3 */
/* additionally takes the current nesting depth */
/* case distinction according to the last applied rule */
ppwriteAux(Stream,Term,Nest) :-
    Term =.. [Op|[Seq]],
    tab(Stream,Nest+2),
    write(Stream,'\\infer[\\'),
    write(Stream,Op),
    write(Stream,']{'),
    ppwriteNest(Stream,Seq),
    write(Stream,'}{'),
    nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
    Term =.. [Op|[Seq|[List]]],
    Op == lower,
    tab(Stream,Nest+2),
    write(Stream,'\\infer[\\Lower]{'),
    ppwriteNest(Stream,Seq),write(Stream,'}{'), nl(Stream),
    ppwriteList(Stream,List,Nest+2),
    nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
    Term =.. [Op|[Seq|[List]]],
    tab(Stream,Nest+2),
    write(Stream,'\\infer[\\'),
    write(Stream,Op),
    write(Stream,']{'),
    ppwriteNest(Stream,Seq),write(Stream,'}{'), nl(Stream),
    ppwriteList(Stream,List,Nest+2),
    nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
/* catches all other cases */
ppwriteAux(Stream,Term,Nest) :-
    Term =.. [Op|[Seq|[List]]],
    Op \== =>, tab(Stream,Nest+2),
    write(Stream,'\\infer['),write(Stream,Op), write(Stream,']{'),
    ppwriteNest(Stream,Seq),write(Stream,'}{'), nl(Stream),
    ppwriteList(Stream,List,Nest+2),
    nl(Stream),tab(Stream,Nest+3),write(Stream,'}').


/* LaTex nested sequents */
ppwriteNest(Stream,ns((Gamma => Delta),Lbl,Suc)) :-
    strip_invisible(Gamma,Sigma),
    strip_invisible(Delta,Pi),
    ppwriteFList(Stream,Sigma),
    write(Stream,' \\seq['),
    ppwriteFList(Stream,Lbl),
    write(Stream,'] '),
    ppwriteFList(Stream,Pi),
    ppwriteNestList(Stream,Suc).


/* LaTex a list of nested sequents */
ppwriteNestList(_,[]).
ppwriteNestList(Stream,[Ns|Tail]) :-
    write(Stream,' \\, [ '),
    ppwriteNest(Stream,Ns),
    write(Stream,' ] '),
    ppwriteNestList(Stream,Tail).


/* LaTeX a list of premisses */
ppwriteList(_,[],_).
ppwriteList(Stream,[H|[]],Nest) :-
	ppwriteAux(Stream,H,Nest).
ppwriteList(Stream,[H|Tl],Nest) :-
	ppwriteAux(Stream,H,Nest),
	nl(Stream),tab(Stream,Nest+2),write(Stream,'&'), nl(Stream),
	ppwriteList(Stream,Tl,Nest).


/* LaTeX a list of sequents */
ppwriteseqlist(Stream,[]) :- write(Stream,'').
ppwriteseqlist(Stream,[(Gamma => Delta)|[]]) :-
    strip_invisible(Gamma,Sigma),
    strip_invisible(Delta,Pi),
    ppwriteFList(Stream,Sigma),write(Stream,' \\seq '),ppwriteFList(Stream,Pi).
ppwriteseqlist(Stream,[(Gamma => Delta),Seq|Hist]) :-
    strip_invisible(Gamma,Sigma),
    strip_invisible(Delta,Pi),
    ppwriteFList(Stream,Sigma),write(Stream,' \\seq '),ppwriteFList(Stream,Pi),
    write(Stream,' \\lns '),ppwriteseqlist(Stream,[Seq|Hist]).


/* LaTeX a list of formulae */
ppwriteFList(_,[]).
ppwriteFList(Stream,[inv(_)|Tail]) :-
    ppwriteFList(Stream,Tail).
ppwriteFList(Stream,[Fml|[]]) :-
    ppwriteFml(Stream,Fml).
ppwriteFList(Stream,[H,G|Tail]) :-
    ppwriteFml(Stream,H),write(Stream,','),ppwriteFList(Stream,[G|Tail]).


/* LaTeX a formula */
ppwriteFml(Stream,false) :-
	write(Stream,' \\bot ').
ppwriteFml(Stream,true) :-
	write(Stream,' \\top ').
ppwriteFml(Stream,Term) :-
	atom(Term), write(Stream,Term).
ppwriteFml(Stream,neg(Fml)) :-
    write(Stream,' \\neg '),
    ppwriteFml(Stream,Fml).
ppwriteFml(Stream,ea(Fml)) :-
    write(Stream,' \\nea '),
    ppwriteFml(Stream,Fml).
ppwriteFml(Stream,aa(Fml)) :-
    write(Stream,' \\naa '),
    ppwriteFml(Stream,Fml).
ppwriteFml(Stream,and(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\land '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,or(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\lor '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,->(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\to '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,nesfin(Gamma => Delta,[])) :-
    write(Stream,'\\nesfin{'),
    ppwriteFList(Stream,Gamma),
    write(Stream,' \\seq '),
    ppwriteFList(Stream,Delta),
    write(Stream,'}').
ppwriteFml(Stream,nesunf(Gamma => Delta,[])) :-
    write(Stream,'\\nesunf{'),
    ppwriteFList(Stream,Gamma),
    write(Stream,' \\seq '),
    ppwriteFList(Stream,Delta),
    write(Stream,'}').


/* strip_invisible /2 */
/* strips invisible formulae from a list of formulae */
strip_invisible([],[]).
strip_invisible([inv(_)|Tail],Sigma) :- strip_invisible(Tail,Sigma).
strip_invisible([F|Tail],[F|Sigma]) :- strip_invisible(Tail,Sigma).


/* strip_nonformulae /2
 * strips all non-formulae from a list
*/
strip_nonformulae([],[]).
strip_nonformulae([inv(_)|Tail],Sigma) :-
    strip_nonformulae(Tail,Sigma).
strip_nonformulae([nesfin(_,_)|Tail],Sigma) :-
    strip_nonformulae(Tail,Sigma).
strip_nonformulae([nesunf(_,_)|Tail],Sigma) :-
    strip_nonformulae(Tail,Sigma).
strip_nonformulae([F|Tail],[F|Sigma]) :- 
    strip_nonformulae(Tail,Sigma).


/* ppwriteNbh /2
 * LaTex a list of sets of worlds
*/
ppwriteNbh(_,[]).
ppwriteNbh(Stream,[Set|[]]) :-
    (Set = empty,
     write(Stream,' \\emptyset ')
     ;
     Set = self,
     write(Stream,' \\{ \\text{self} \\} ') 
     ;
     \+ Set = empty,
    write(Stream,' \\{ '),
    ppwriteSet(Stream,Set),
    write(Stream,' \\} ')).
ppwriteNbh(Stream,[Set1,Set2|Tail]) :-
    (Set1 = empty,
     write(Stream,' \\emptyset , ')
     ;
     \+ Set1 = empty,
    write(Stream,' \\{ '),
    ppwriteSet(Stream,Set1),
    write(Stream,' \\} ')),
    ppwriteNbh(Stream,[Set2|Tail]).


/* ppwriteSet /2
 * LaTex a set of worlds
*/
ppwriteSet(_,[]).
ppwriteSet(Stream,[Name|[]]) :-
    ppwriteWorld(Stream,Name).
ppwriteSet(Stream,[Name1,Name2|Tail]) :-
    ppwriteWorld(Stream,Name1),
    write(Stream,', '),
    ppwriteSet(Stream,[Name2|Tail]).


/* ppwriteWorld /2
 * LaTex the name of a world
*/
ppwriteWorld(Stream,World) :-
    reverse(World,Dlorw),
    ppwriteWorldAux(Stream,Dlorw).
ppwriteWorldAux(_,[]).
ppwriteWorldAux(Stream,[N|[]]) :-
    write(Stream,N),!.
ppwriteWorldAux(Stream,[N,M|Tail]) :-
    write(Stream,N),write(Stream,'.'),
    ppwriteWorldAux(Stream,[M|Tail]),!.


/* LaTeXing the countermodel */
ppwriteModelNew(Stream,NS) :-
    write(Stream,'\\bigskip'),
    nl(Stream),nl(Stream),
    write(Stream,'\\begin{adjustbox}{max width=\\textwidth}'),nl(Stream),
    write(Stream,'\\begin{tikzpicture}[world/.style={circle,draw,fill=blue!20}]'),
    nl(Stream),
    ppwriteModelAuxNew(Stream,0,[],co(0,0),[NS],_,_),
    write(Stream,'\\end{tikzpicture}'),nl(Stream),
    nl(Stream),write(Stream,'\\end{adjustbox}'),nl(Stream).
    

/* ppwriteModelAuxNew: takes as input the stream, a nesting operator
 * for printing to the file, the current starting coordinate and a
 * list of nested sequents. Prints the head of the successors at the
 * specified coordinate, increases the coordinate, calls itself on the
 * tail, then outputs a list with the coordinates of the successors
 * and the resulting coordinate.
*/
ppwriteModelAuxNew(_,_,CoList,co(X,Y),[],CoList,co(X,Y)).
ppwriteModelAuxNew(Stream,Nest,CoList,co(X,Y),[mod(Name,Lbl,(Gamma => Delta),Nbh,Suc)|Tail],CoListNew,co(X1,Y1)) :-
    list_to_set(Gamma,Sigma),
    strip_invisible(Sigma,Pi),
    list_to_set(Delta,Omega),
    strip_nonformulae(Omega,Theta),
    nl(Stream),tab(Stream,Nest+2),
    write(Stream,'\\node [world,label=right:{'),
    ppwriteWorld(Stream,Name),
    write(Stream,'; \\begin{tabular}{l}True formulae: $'),
    ppwriteFList(Stream,Pi),
    write(Stream,' $; False formulae: $'),
    ppwriteFList(Stream,Theta),
    write(Stream,'$ \\\\'),
    write(Stream,'Neighbourhoods: $ '),
    (Nbh = [],
     write(Stream, '\\emptyset')
     ;
     Nbh = [ self ],
     write(Stream, ' \\{\\;\\{ '),
     ppwriteWorld(Stream,Name),
     write(Stream, '\\}\\;\\} ')
     ;
     \+ Nbh = [],
     \+ Nbh = [ self ],
     write(Stream,' \\{ '),
    ppwriteNbh(Stream,Nbh),
    write(Stream,' \\}')),
    write(Stream,'$ \\end{tabular}}] ('),
    write(Stream,X),
    write(Stream,'and'),
    write(Stream,Y),
    write(Stream,') at ('),
    write(Stream,X),
    write(Stream,','),
    write(Stream,Y),
    write(Stream,') {};'),
    (Nbh = [ self ],
     nl(Stream),tab(Stream,Nest+2),
     write(Stream,'\\draw[->] ('),
     write(Stream,X),
     write(Stream,'and'),
     write(Stream,Y),
     write(Stream,') .. controls +(130:.75cm) and +(50:.75cm) .. ('),
     write(Stream,X),
     write(Stream,'and'),
     write(Stream,Y),
     write(Stream,');')
    ;
    true),
    X2 is X + 1,
    Y2 is Y + 1,
    ppwriteModelAuxNew(Stream,Nest+2,[],co(X2,Y2),Suc,SucCoList,co(_,Y3)),
    write(Stream,'\\foreach \\point in {'),
    writeCoList(Stream,SucCoList),
    write(Stream,'}'),
    nl(Stream),
    tab(Stream,Nest+4),
    write(Stream,'\\draw[->] ('),
    write(Stream,X),write(Stream,'and'),write(Stream,Y),write(Stream,') .. controls +(up:.5cm) and +(left:.7cm) .. (\\point);'),
    nl(Stream),tab(Stream,Nest+2),
    ppwriteModelAuxNew(Stream,Nest,[co(X,Y)|CoList],co(X,Y3),Tail,CoListNew,co(X1,Y1)).


/* Old ONE: */
ppwriteModelAuxOld(_,_,CoList,co(X,Y),[],CoList,co(X,Y)).
ppwriteModelAuxOld(Stream,Nest,CoList,co(X,Y),[ns((Gamma => _),_,Suc)|Tail],CoListNew,co(X1,Y1)) :-
    list_to_set(Gamma,Sigma),
    strip_invisible(Sigma,Pi),
    nl(Stream),tab(Stream,Nest+2),
    write(Stream,'\\node [world,label=right:{$'),
    ppwriteFList(Stream,Pi),
    write(Stream,'$}] ('),
    write(Stream,X),
    write(Stream,'and'),
    write(Stream,Y),
    write(Stream,') at ('),
    write(Stream,X),
    write(Stream,','),
    write(Stream,Y),
    write(Stream,') {};'),
    X2 is X + 1,
    Y2 is Y + 1,
    ppwriteModelAuxOld(Stream,Nest+2,[],co(X2,Y2),Suc,SucCoList,co(_,Y3)),
    write(Stream,'\\foreach \\point in {'),
    writeCoList(Stream,SucCoList),
    write(Stream,'}'),
    nl(Stream),
    tab(Stream,Nest+4),
    write(Stream,'\\draw[->] ('),
    write(Stream,X),write(Stream,'and'),write(Stream,Y),write(Stream,') -- (\\point);'),
    nl(Stream),tab(Stream,Nest+2),
    ppwriteModelAuxOld(Stream,Nest,[co(X,Y)|CoList],co(X,Y3),Tail,CoListNew,co(X1,Y1)).
	 
writeCoList(_,[]).
writeCoList(Stream,[co(X,Y)|[]]) :-
    write(Stream,X),write(Stream,'and'),write(Stream,Y).
writeCoList(Stream,[co(X,Y),co(Z,W)|Tail]) :-
    write(Stream,X),write(Stream,'and'),write(Stream,Y),write(Stream,','),
    writeCoList(Stream,[co(Z,W)|Tail]).

/* END OF MODEL LATEXING */

