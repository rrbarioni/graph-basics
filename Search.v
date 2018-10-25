Add LoadPath "C:\Users\rrb\Documents\graph-basics".
Require Export Graphs.

Section SEARCH.

Inductive AdjListElem : Type :=
  | ALE : Vertex -> V_list -> AdjListElem.

Inductive AdjList : Type :=
  | AL_empty : AdjList
  | AL : AdjListElem -> AdjList -> AdjList.

Fixpoint AdjList_receiving_Arc (a : Arc) (al : AdjList) :
 AdjList :=
  match al with
  | AL_empty => AL (ALE (A_tail a) (cons (A_head a) nil)) al
  | AL (ALE (index vi) l) al' =>
      match (A_tail a) with
      | index aat =>
          if beq_nat aat vi
          then AL (ALE (index vi) (cons (A_tail a) l)) al
          else AL (ALE (index vi) l) (AdjList_receiving_Arc a al')
      end
  end.

Fixpoint A_list_to_AdjList (a : A_list) (al : AdjList) :
 AdjList :=
  match a with
  | nil => al
  | h :: t => A_list_to_AdjList t (AdjList_receiving_Arc h al)
  end.

Fixpoint Graph_to_AdjList (v : V_set) (a : A_set) (g : Graph v a) {struct g} :
 AdjList :=
  A_list_to_AdjList (GA_list v a g) AL_empty.

Compute (Graph_to_AdjList V_empty A_empty G_empty).

End SEARCH.