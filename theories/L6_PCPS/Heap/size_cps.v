From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions.

From L6.Heap Require Import heap heap_defs cc_log_rel
     closure_conversion closure_conversion_util compat.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

Require Import compcert.lib.Maps.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module Size (H : Heap).

  (* This is stupid. Find out how to use modules correctly. *)
  Module C := Compat H.

  Import H C C.LR C.LR.Sem C.LR.Sem.Equiv C.LR.Sem.Equiv.Defs.

  (** * Size of CPS terms, values and environments, needed to express the upper bound on
         the execution cost of certain transformations *)
  
  (** The size of CPS expressions. Right now we only count the number of
   * variables in a program (free or not), the number of functions and
   * the number of function definition blocks *)
  (* TODO -- max per function block *)
  Fixpoint exp_num_vars (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => length ys + exp_num_vars e
      | Ecase x l =>
        1 + (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => exp_num_vars e + sizeOf_l l
               end) l
      | Eproj x _ _ y e => 1 + exp_num_vars e
      | Efun B e => 1 + fundefs_num_vars B + 2 * numOf_fundefs B + exp_num_vars e
      | Eapp x _ ys => 1 + length ys
      | Eprim x _ ys e => length ys + exp_num_vars e
      | Ehalt x => 1
    end
  with fundefs_num_vars (B : fundefs) : nat := 
         match B with
           | Fcons _ _ xs e B =>
             1 + exp_num_vars e + fundefs_num_vars B
           | Fnil => 0
         end.

  Fixpoint max_vars_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => max_vars_exp e
      | Ecase x l =>
        1 + (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => max_vars_exp e
               end) l
      | Eproj x _ _ y e => 1 + exp_num_vars e
      | Efun B e => max (fundefs_num_vars B) (max_vars_exp e)
      | Eapp x _ ys => 0
      | Eprim x _ ys e => exp_num_vars e
      | Ehalt x => 0
    end.

  Fixpoint exp_num_vars_out (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => length ys
      | Ecase x l => 1
      | Eproj x _ _ y e => 1  
      | Efun B e => 1 + fundefs_num_vars B + 3 * numOf_fundefs B
      | Eapp x _ ys => 1 + length ys
      | Eprim x _ ys e => length ys 
      | Ehalt x => 1
    end.

  Fixpoint max_num_vars_out (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => 0
      | Ecase x l => 0
      | Eproj x _ _ y e => 0
      | Efun B e => 1 + fundefs_num_vars B 
      | Eapp x _ ys => 0
      | Eprim x _ ys e => 0 
      | Ehalt x => 0
    end.

  (** The cost of evaluating a CC evaluation context *)
  Fixpoint cost_exp_ctx (c : exp_ctx) : nat :=
    match c with
      | Hole_c => 0
      | Econstr_c _ _ ys c => 1 + length ys + cost_exp_ctx c
      | Eproj_c _ _ _ _ c => 1 + cost_exp_ctx c
      | Efun1_c B c => 1 + cost_exp_ctx c 
      | Eprim_c _ _ ys c => length ys + cost_exp_ctx c
      | Ecase_c _ l1 _ c l2 => 0
      | Efun2_c B e => 0
    end.

  Definition max_vars_value (v : value) : nat :=
    match v with
      | Loc _ => 0
      | FunPtr B _ => fundefs_num_vars B
    end.

  Definition max_vars_block (b : block) : nat :=
    match b with
      | Constr _ vs => max_list_nat_with_measure max_vars_value 0 vs
      | Clos v1 v2 => max (max_vars_value v1) (max_vars_value v2)
      | Env x => 0
    end.

  Definition max_vars_heap (S : Ensemble loc) `{ToMSet S} (H : heap block) :=
    size_with_measure_filter max_vars_block (reach_set H mset) H.
  
  Definition max_heap_exp (S : Ensemble loc) `{ToMSet S} (H : heap block) (e : exp) :=
    max (max_vars_heap S H) (max_vars_exp e).
  
  (** * Postcondition *)

  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition Post
             k (* time units already spent *)
             (p1 p2 : heap block * env * exp * nat * nat) :=
    match p1, p2 with
      | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
        c1 <= c2 + k <=  c1 * (1 + 2 * max_heap_exp (env_locs rho1 (occurs_free e1)) H1 e1) + (exp_num_vars_out e1) /\
        m1 <= m2 <= m1 * (4 + max_heap_exp (env_locs rho1 (occurs_free e1)) H1 e1)
    end.
  
  (** * Precondition *)

  (** Enforces that the initial heaps have related sizes *)
  Definition Pre
             C (* Context already processed *)
             (p1 p2 : heap block * env * exp) :=
    let m := cost_alloc_ctx C in 
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        size_heap H1 + m <= size_heap H2 + max_num_vars_out e1 <= (size_heap H1) * (4 + max_heap_exp (env_locs rho1 (occurs_free e1)) H1 e1) + m
    end.
  
  (** Compat lemmas *)

  Lemma PostBase H1 H2 rho1 rho2 e1 e2 C k :
    k <= exp_num_vars_out e1 ->
    cost_alloc_ctx C = max_num_vars_out e1 ->
    InvCostBase (Post k) (Pre C) H1 H2 rho1 rho2 e1 e2.
  Proof.
    unfold InvCostBase, Post, Pre.
    intros H1' rho1' H2' rho2' c b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hsize.
    split.
    + split. omega. eapply plus_le_compat.
      rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
      now eapply le_plus_l. omega.
    + split. omega. 
      omega.
  Qed.


  Lemma PostConstrCompat H1 H2 rho1 rho2 x1 x2 c ys1 ys2 e1 e2 k :
    length ys1 = length ys2 ->
    k <= length ys1 ->
    InvCtxCompat (Post k) (Post 0)
                 H1 H2 rho1 rho2 (Econstr_c x1 c ys1 Hole_c) (Econstr_c x2 c ys2 Hole_c) e1 e2.
  Proof.
    unfold InvCtxCompat, Post.
    intros Hlen Hleq H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 b1 b2 Heq1 Hinj1 Heq2 Hinj2 [[Hc1 Hc2] [Hm1 Hm2]] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    rewrite !plus_O_n in *. simpl (cost_ctx _) in *.
    rewrite !Hlen in *. split.
    - split. omega. simpl (exp_num_vars_out _).
      eapply plus_le_compat; [| omega ].
      simpl (max_heap_exp _ _ _) in *.
      rewrite <- !plus_n_O in *.
      eapply le_trans. 
      eapply plus_le_compat_r. eassumption.
      admit.
    - split; eauto.
      eapply le_trans. eassumption. admit.
  Admitted. 

  Lemma PreConstrCompat H1 H2 rho1 rho2 x1 x2 c ys1 ys2 e1 e2 C :
    IInvCtxCompat (Pre C) (Pre Hole_c)
                 H1 H2 rho1 rho2 (Econstr_c x1 c ys1 Hole_c) (Econstr_c x2 c ys2 Hole_c) e1 e2.
  Proof.
    unfold IInvCtxCompat, Pre.
    intros H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2' 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 [Hm1 Hm2] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    split.
    - simpl. simpl in Hm1. admit.
    - omega. 
    
  Lemma PostProjCompat H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2 k :
    InvCtxCompat (Post k) (Post 0)
                 H1 H2 rho1 rho2 (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.

  Lemma PreProjCompat H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2 C :
    IInvCtxCompat (Pre C) (Pre Hole_c)
                  H1 H2 rho1 rho2 (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.
  
  

  

  Lemma sizeOf_env_setlist k H rho rho' xs vs :
    setlist xs vs rho = Some rho' ->
    sizeOf_env k H rho' =
    max (max_list_nat_with_measure (sizeOf_val k H) 0 vs) (sizeOf_env k H rho).
  Proof.
    revert vs rho rho'. induction xs; intros vs rho rho' Hset.
    - destruct vs; try discriminate. inv Hset.
      reflexivity.
    - destruct vs; try discriminate.
      simpl in Hset. destruct (setlist xs vs rho) eqn:Hset'; try discriminate.
      inv Hset. rewrite sizeOf_env_set; simpl.
      rewrite max_list_nat_acc_spec.
      rewrite <- Max.max_assoc. eapply NPeano.Nat.max_compat. reflexivity.
      eauto.
  Qed.

  Lemma sizeOf_env_get k H rho x v :
    rho ! x = Some v ->
    sizeOf_val k H v <= sizeOf_env k H rho.
  Proof.
    intros Hget. 
    unfold sizeOf_env. rewrite <- sizeOf_val_eq.
    eapply max_ptree_with_measure_spec1.
    eassumption.
  Qed.

  (** Lemmas about [size_of_exp] *)

  Lemma sizeOf_exp_grt_1 e :
    1 <= sizeOf_exp e.
  Proof.
    induction e using exp_ind'; simpl; eauto; omega.
  Qed.

  (** Lemmas about [sizeOf_exp_ctx] *)
  Lemma sizeOf_exp_ctx_comp_ctx_mut :
    (forall C1 C2,
       sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2) /\
    (forall B e,
       sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e).
  Proof.
    exp_fundefs_ctx_induction IHe IHB; 
    try (intros C; simpl; eauto; rewrite IHe; omega);
    try (intros C; simpl; eauto; rewrite IHB; omega).
    (* probably tactic misses an intro pattern *)
    intros l' C. simpl. rewrite IHe; omega.
  Qed.

  Corollary sizeOf_exp_ctx_comp_ctx :
    forall C1 C2,
      sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2.
  Proof.
    eapply sizeOf_exp_ctx_comp_ctx_mut; eauto.
  Qed.

  Corollary sizeOf_fundefs_ctx_comp_f_ctx :
    forall B e,
      sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e.
  Proof.
    eapply sizeOf_exp_ctx_comp_ctx_mut; eauto.
  Qed.
  
  (** Lemmas about [max_exp_env] *)

  Lemma max_exp_env_grt_1 k H rho e :
    1 <= max_exp_env k H rho e.
  Proof.
    unfold max_exp_env.
    eapply le_trans. now apply sizeOf_exp_grt_1.
    eapply Max.le_max_l.
  Qed.

  Lemma max_exp_env_Econstr k H x t ys e rho :
    max_exp_env k H rho e <= max_exp_env k H rho (Econstr x t ys e).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.
  
  Lemma max_exp_env_Eproj k x t N y e H rho :
    max_exp_env k H rho e <= max_exp_env k H rho (Eproj x t N y e).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Ecase_cons_hd k x c e l H rho :
    max_exp_env k H rho e <= max_exp_env k H rho (Ecase x ((c, e) :: l)).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.
  
  Lemma max_exp_env_Ecase_cons_tl k x c e l H rho :
    max_exp_env k H rho  (Ecase x l) <= max_exp_env k H rho (Ecase x ((c, e) :: l)).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Eprim k H rho x f ys e :
    max_exp_env k H rho e <= max_exp_env k H rho (Eprim x f ys e).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  (** Number of function definitions *)
  Fixpoint numOf_fundefs (B : fundefs) : nat := 
    match B with
      | Fcons _ _ xs e B =>
        1 + numOf_fundefs B
      | Fnil => 0
    end.

  (** Number of function definitions in an expression *)
  Fixpoint numOf_fundefs_in_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => numOf_fundefs_in_exp e
      | Ecase x l =>
        1  + (fix num l :=
                match l with
                  | [] => 0
                  | (t, e) :: l => numOf_fundefs_in_exp e + num l
                end) l
      | Eproj x _ _ y e => 1 + numOf_fundefs_in_exp e
      | Efun B e => numOf_fundefs_in_fundefs B + numOf_fundefs_in_exp e
      | Eapp x _ ys => 0
      | Eprim x _ ys e => numOf_fundefs_in_exp e
      | Ehalt x => 0
    end
  with numOf_fundefs_in_fundefs (B : fundefs) : nat :=
         match B with
           | Fcons _ _ xs e B =>
             1 + numOf_fundefs_in_exp e + numOf_fundefs_in_fundefs B
           | Fnil => 0
         end.

  Lemma numOf_fundefs_le_sizeOf_fundefs B :
    numOf_fundefs B <= sizeOf_fundefs B.
  Proof.
    induction B; eauto; simpl; omega.
  Qed.


  (* Lemma max_exp_env_Efun k B e rho : *)
  (*   max_exp_env k He (def_funs B B rho rho) <= max_exp_env k (Efun B e) rho. *)
  (* Proof. *)
  (*   unfold max_exp_env. eapply le_trans. *)
  (*   - eapply NPeano.Nat.max_le_compat_l. *)
  (*     now apply sizeOf_env_def_funs. *)
  (*   - rewrite (Max.max_comm (sizeOf_env _ _)), Max.max_assoc. *)
  (*     eapply NPeano.Nat.max_le_compat_r. *)
  (*     eapply Nat.max_lub; simpl; omega. *)
  (* Qed. *)

    (* Concrete bounds for closure conversion *)


  (** * Properties of the cost invariants *)

  (** Transfer units from the accumulator to the cost of e2 *)
  Lemma Post_transfer i (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp)
        (k c1 c2 c m1 m2 : nat) : 
    Post (k + c) i (H1, rho1, e1, c1, m1) (H2, rho2, e2, c2, m2) ->
    Post k i (H1, rho1, e1, c1, m1) (H2, rho2, e2, c2 + c, m2).
  Proof.
    simpl. intros H. omega.
  Qed.

  Lemma Post_timeout i (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp)
        C (k c  : nat) :
    Pre C i (H1, rho1, e1) (H2, rho2, e2) ->
    k <= 7 * sizeOf_exp e1 ->
    cost_alloc_ctx C = 0 ->
    PostL k i H1 rho1 e1 (c, size_heap H1) (c, size_heap H2).
  Proof. 
    unfold Pre, Post. intros [H1' H2'] Ht Hm.
    split. split. omega.
    assert (Hgrt := max_exp_env_grt_1 i H1 rho1 e1).
    eapply plus_le_compat; try omega.
    replace c with (1 * c * 1) at 1 by omega. 
    eapply mult_le_compat. omega. eassumption.
    rewrite Hm in *. split. omega.
    rewrite <- plus_n_O in H2'. eassumption.
  Qed.

  (* Cost for projecting vars *)
  Lemma project_var_cost 
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_var Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    sizeOf_exp_ctx C1 <= 1.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.
  
  Lemma project_vars_cost 
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_vars Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    sizeOf_exp_ctx C1 <= length x.
  Proof.
    intros Hvar. induction Hvar; eauto.
    rewrite sizeOf_exp_ctx_comp_ctx.
    simpl. replace (S (length ys)) with (1 + length ys) by omega.
    eapply plus_le_compat.
    eapply project_var_cost; eauto.
    eauto.
  Qed.

  Lemma project_var_cost_alloc
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_var Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    cost_alloc_ctx C1 = 0.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.
  
  Lemma project_vars_cost_alloc
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_vars Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    cost_alloc_ctx C1 = 0.
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. rewrite cost_alloc_ctx_comp_ctx_f.
    erewrite project_var_cost_alloc; eauto.
  Qed.

  Lemma make_closures_cost ct B S Γ C g :
    make_closures ct B S Γ C g S ->
    sizeOf_exp_ctx C = 3 * (numOf_fundefs B).
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. omega.
  Qed.

  Lemma make_closures_cost_alloc ct B S Γ C g :
    make_closures ct B S Γ C g S ->
    cost_alloc_ctx C = 3 * (numOf_fundefs B).
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. omega.
  Qed.

  (* Lemma ctx_to_heap_env_cost C H1 rho1 H2 rho2 m : *)
  (*   ctx_to_heap_env C H1 rho1 H2 rho2 m -> *)
  (*   m = sizeOf_exp_ctx C. *)
  (* Proof. *)
  (*   intros Hctx; induction Hctx; eauto. *)
  (*   simpl. omega. *)
  (*   simpl. omega. *)
  (*   simpl. omega. *)
  (* Qed.  *)
  
End Size.