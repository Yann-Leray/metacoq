From MetaCoq.PCUIC Require Import PCUICAst.

Theorem relevance_subst u s : relevance_of_sort (subst_instance_univ u s) = relevance_of_sort s.
Proof.
  destruct s; reflexivity.
Qed.
