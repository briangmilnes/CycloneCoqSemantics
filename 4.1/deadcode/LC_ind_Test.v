(* I can setup the right induction but I can't get it to 
take my st_pred in the definition, which is odd. *)

Function open_rec_v_tm_st_close_rec_v_tm_st_pred (t : St) (lc' : lc_st t):=
  lc_st t -> 
  forall x n, 
    open_rec_v_tm_st n x (close_rec_v_tm_st n x t)  = t.
Hint Unfold open_rec_v_tm_st_close_rec_v_tm_st_pred.


Function open_rec_v_tm_e_close_rec_v_tm_e_pred (t : E) (lc' : lc_e t):=
  lc_e t -> 
  forall x n, 
    open_rec_v_tm_e n x (close_rec_v_tm_e n x t)  = t.
Hint Unfold open_rec_v_tm_e_close_rec_v_tm_e_pred.

Function open_rec_v_tm_f_close_rec_v_tm_f_pred (t : F) (lc' : lc_f t) :=
  lc_f t -> 
  forall x n, 
    open_rec_v_tm_f n x (close_rec_v_tm_f n x t)  = t.
Hint Unfold open_rec_v_tm_f_close_rec_v_tm_f_pred.

Print lc_st_ind_mutual.

Ltac open_rec_v_tm_X_close_rec_v_tm_X_induction MIS :=
  apply (MIS 
           open_rec_v_tm_st_close_rec_v_tm_st_pred
           open_rec_v_tm_e_close_rec_v_tm_e_pred
           open_rec_v_tm_f_close_rec_v_tm_f_pred).
           
Lemma test: 
  forall t, 
    lc_st t ->
    forall x n, 
      open_rec_v_tm_st n x (close_rec_v_tm_st n x t)  = t.
Proof.
  unfold open_rec_v_tm_st_close_rec_v_tm_st_pred.
  apply (lc_st_ind_mutual
          (fun (t : St) (lc' :  lc_st t) =>
             forall x n, 
             open_rec_v_tm_st n x (close_rec_v_tm_st n x t)  = t)

          (fun (t : E) (lc' : lc_e t) => 
               forall x n, 
                 open_rec_v_tm_e n x (close_rec_v_tm_e n x t)  = t)

          (fun (t : F)  (lc' : lc_f t) =>
              forall x n, 
                open_rec_v_tm_f n x (close_rec_v_tm_f n x t)  = t)).
  Focus 22.

  open_rec_v_tm_X_close_rec_v_tm_X_induction lc_st_ind_mutual.
Admitted.
