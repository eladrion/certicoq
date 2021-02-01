From Coq Require Import ZArith.ZArith Lists.List Strings.String micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.

Import ListNotations.

Require Import L4.expression L4.fuel_sem.

(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Classes.Morphisms. *)
(* Require Import Coq.Classes.RelationClasses. *)

Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        tactics L4_to_L6 L4_to_L6_util L4_to_L6_corresp
        L6.tactics identifiers bounds cps_util rename. 

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.

Section Bounds.

  Global Instance L4_resource_nat : @L4_resource nat.
  Proof.
    econstructor.
  Defined.   
  
  Global Instance L4_fuel_resource_nat : @L4_fuel_resource nat.
  Proof.
    econstructor; tci.
  Defined.

  Global Program Instance trace_res_pre : @resource fin unit :=
    { zero := tt;
      one_i fin := tt;
      plus x y := tt; }.
  Next Obligation. destruct x. reflexivity. Qed.
  Next Obligation. destruct x; destruct y. reflexivity. Qed.

  
  Global Program Instance trace_res_exp : @exp_resource unit :=
    { HRes := trace_res_pre }.
  
  Global Instance trace_res : @trace_resource unit.
  Proof.
    econstructor. eapply trace_res_exp.
  Defined.
    
  Definition eq_fuel : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => f1 = f2.

  Definition cps_bound (f_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2)%nat.

  Definition cps_bound_exps (f_src : nat) : @PostT nat unit :=
    fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) =>
      (f1 + f_src <= f2 + 1)%nat.

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.
  
  
  
  Global Instance eq_fuel_compat cenv :
    @Post_properties cenv nat _ unit _ eq_fuel eq_fuel eq_fuel. 
  Proof.
    unfold eq_fuel. constructor; try now (intro; intros; intro; intros; unfold_all; simpl; lia).
    - intro; intros. unfold post_base'. unfold_all; simpl. lia.
    - firstorder.
  Qed. 

End Bounds.


Section FV.

  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map).
  
  Definition cps_cvt_exp_fv_stmt :=
    forall e e' k1 vars1 S1 S2,
      cps_cvt_rel func_tag kon_tag default_tag S1 e vars1 k1 cnstrs S2 e' ->
      occurs_free e' \subset k1 |: FromList vars1 :|: S1.

  Definition cps_cvt_exps_fv_stmt :=
    forall e e' e_app vars1 ks xs S1 S2,
      Disjoint _ (FromList ks) S1 ->
      cps_cvt_rel_exps func_tag kon_tag default_tag S1 e vars1 e_app xs ks cnstrs S2 e' ->
      occurs_free e_app \subset FromList ks :|: FromList vars1 :|: S1 ->
      (* XXX wrong stmt *)
      occurs_free e' \subset FromList vars1 :|: S1.

  Definition cps_cvt_efnlst_fv_stmt :=
    forall S1 efns vars1 nlst1 S2 fdefs1,
      cps_cvt_rel_efnlst func_tag kon_tag default_tag S1 efns vars1 nlst1 cnstrs S2 fdefs1 ->
      occurs_free_fundefs fdefs1 \subset FromList vars1 :|: S1.

  Definition cps_cvt_branches_fv_stmt :=
    forall S1 bs vars1 k1 x1 S2 bs1 x,
      cps_cvt_rel_branches func_tag kon_tag default_tag S1 bs vars1 k1 x1 cnstrs S2 bs1 ->
      occurs_free (Ecase x bs1) \\ [set x] \subset S1.
  
  
  Definition cps_cvt_rel_fv_stmt :=
    cps_cvt_exp_fv_stmt /\
    cps_cvt_exps_fv_stmt /\
    cps_cvt_efnlst_fv_stmt /\
    cps_cvt_branches_fv_stmt.
  

  Lemma cps_cvt_rel_fv : cps_cvt_rel_fv_stmt. 
  Admitted. 

  
  Corollary cps_cvt_exp_fv : cps_cvt_exp_fv_stmt.
  Proof. eapply (proj1 cps_cvt_rel_fv). Qed.

  (* Corollary cps_cvt_exps_fv : cps_cvt_exps_fv_stmt. *)
  (* Proof. eapply (proj1 (proj2 cps_cvt_rel_fv)). Qed. *)

  (* Corollary cps_cvt_efnlst_fv : cps_cvt_efnlst_fv_stmt. *)
  (* Proof. eapply (proj1 (proj2 (proj2 cps_cvt_rel_fv))). Qed. *)

  (* Corollary cps_cvt_branches_fv : cps_cvt_branches_fv_stmt. *)
  (* Proof. eapply (proj2 (proj2 (proj2 cps_cvt_rel_fv))). Qed. *)


End FV. 

Section Correct.

  Context (prim_map : M.t (kername * string (* C definition *) * nat (* arity *))). 
  Context (func_tag kon_tag default_tag default_itag : positive)
          (cnstrs : conId_map)                      
          (cenv : ctor_env).

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold algebra.one in *;
    try unfold one_i in *;
    try unfold algebra.HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.

  
  Definition cps_cvt_rel := L4_to_L6.cps_cvt_rel func_tag kon_tag default_tag.
  Definition cps_cvt_rel_exps := L4_to_L6.cps_cvt_rel_exps func_tag kon_tag default_tag.
  Definition cps_cvt_rel_efnlst := L4_to_L6.cps_cvt_rel_efnlst func_tag kon_tag default_tag.
  Definition cps_cvt_rel_branches := L4_to_L6.cps_cvt_rel_branches func_tag kon_tag default_tag.
  Definition cps_env_rel := cps_env_rel cnstrs func_tag kon_tag default_tag.
  Definition cps_val_rel := cps_val_rel cnstrs func_tag kon_tag default_tag.
  
  (* Alpha-equiv corollaries *)
  
  Corollary cps_cvt_exp_alpha_equiv k :
    cps_cvt_exp_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_exps_alpha_equiv k :
    cps_cvt_exps_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.

  Corollary cps_cvt_efnlst_alpha_equiv k :
    cps_cvt_efnlst_alpha_equiv eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.
  
  Corollary cps_cvt_branches_alpha_equiv k :
    cps_cvt_branches_alpha_equiv eq_fuel eq_fuel cnstrs cenv func_tag kon_tag default_tag k.
  Proof. eapply cps_cvt_alpha_equiv; tci. firstorder. Qed.
  
  (** ** Correctness statements *)
  
  Definition cps_cvt_correct_exp (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f : nat) :=
    forall rho vnames k x vk e' S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->
                         
      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->

      cps_env_rel vnames vs rho ->
      M.get k rho = Some vk ->
      
      cps_cvt_rel S e vnames k cnstrs S' e' ->     

      (* Source terminates *)
      (forall v v', r = (Val v) -> cps_val_rel v v' ->
       preord_exp cenv (cps_bound f) eq_fuel i
                  ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val))))
                  (e', rho)) /\
      (* SOurce diverges *)
      (r = fuel_sem.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel cenv rho e' c eval.OOT tt).

  Definition cps_cvt_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f : nat)  :=
    forall rho vnames k x vk e' S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length vnames)) e ->
      
      Disjoint _ (k |: FromList vnames) S ->
      ~ x \in k |: FromList vnames ->
      ~ k \in FromList vnames ->
                      
      cps_env_rel vnames vs rho ->
      M.get k rho = Some vk ->

      cps_cvt_rel S e vnames k cnstrs S' e' ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> cps_val_rel v v' ->
                    preord_exp cenv (cps_bound (f <+> fuel_sem.one e)) eq_fuel i
                               ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val))))
                               (e', rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, ((f <+> fuel_sem.one e) <= c)%nat /\ bstep_fuel cenv rho e' c eval.OOT tt).


  Definition cps_cvt_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f : nat)  :=
    forall rho vnames e' e_app S S' vs2 xs ys ks vs',
      well_formed_env vs ->
      exps_wf (N.of_nat (Datatypes.length vnames)) es ->
      
      Disjoint _ (FromList vnames :|: FromList xs :|: FromList ys :|: FromList ks) S ->

      Disjoint _ (FromList vnames) (FromList xs :|: FromList ys :|: FromList ks) ->
      Disjoint _ (FromList ks) (FromList xs :|: FromList ys) ->
      Disjoint _ (FromList xs) (FromList ys) ->
      NoDup xs ->
      
      cps_env_rel vnames vs rho ->

      Disjoint _ (occurs_free e_app) (FromList ks) ->
      (* M.get k rho = Some vk -> *)
      
      cps_cvt_rel_exps S es vnames e_app xs ks cnstrs S' e' ->
      
      Forall2 (cps_val_rel) vs1 vs2 ->
      get_list ys rho = Some vs' ->
      
      exists rho1,
        set_lists (ys ++ xs) (vs' ++ vs2) rho = Some rho1 /\
        forall i,
          preord_exp cenv (cps_bound f) eq_fuel i (e_app, rho1) (e', rho).

  
  Lemma exps_to_list_inj es1 es2 :
    exps_to_list es1 = exps_to_list es2 ->
    es1 = es2.
  Proof.
    revert es2.
    induction es1; intros es2 Heq; destruct es2; inv Heq.

    reflexivity.

    f_equal. eauto.

  Qed.

  Lemma cps_cvt_rel_exps_app S es es1 es2 vnames e_app xs ks S' e' :
    exps_to_list es = exps_to_list es1 ++ exps_to_list es2 ->
    cps_cvt_rel_exps S es vnames e_app xs ks cnstrs S' e' ->
    exists S'' e'' xs1 xs2 ks1 ks2,
      xs = xs1 ++ xs2 /\
      ks = ks1 ++ ks2 /\
      S'' \subset S /\
      cps_cvt_rel_exps S'' es2 vnames e_app xs2 ks2 cnstrs S' e'' /\
      cps_cvt_rel_exps S es1 vnames e'' xs1 ks1 cnstrs S'' e'.
  Proof.
    revert S es es2 vnames e_app xs ks S' e'.
    induction es1; intros S es es2 vnames e_app xs ks S' e' Heq Hrel. 

    - simpl in Heq. eapply exps_to_list_inj in Heq. subst.
      do 2 eexists. exists []. exists xs. exists []. exists ks. 
      split. reflexivity. split. reflexivity. split. reflexivity. 
      split. eassumption. now econstructor. 

    - destruct es. simpl in Heq. now inv Heq. inv Hrel.

      simpl in *. inv Heq. 

      edestruct IHes1. eassumption. eassumption.
      destructAll. 

      do 2 eexists. exists (x1 :: x2), x3. exists (k1 :: x4), x5.  split; [ | split; [ | split; [ | split ]]].

      reflexivity.  reflexivity.
      
      2:{ eassumption. }
      
      eapply Included_trans. eassumption. 
      eapply Included_trans. eapply cps_cvt_exp_subset. eassumption. now sets.
      
      econstructor; eauto.

  Qed.
      

  Lemma cps_cvt_rel_exps_occurs_free S es vnames e_app xs ks S' e' :
    cps_cvt_rel_exps S es vnames e_app xs ks cnstrs S' e' ->
    Disjoint _ (FromList vnames :|: S) (FromList ks) ->
    NoDup ks ->
    Disjoint _ (occurs_free e') (FromList ks).
  Proof.
    intros Hrel Hdis Hnd.
    induction Hrel.
    - normalize_sets. sets.
    - repeat normalize_occurs_free.
      repeat normalize_sets. simpl.
      repeat rewrite FromList_cons in Hdis at 1. 
      inv Hnd. 
      
      specialize (IHHrel
                    ltac:(eapply cps_cvt_exp_subset in H; eapply Disjoint_Included; [ | | eapply Hdis ]; sets)
                    H3
                 ). 
      eapply Union_Disjoint_r; sets.
      eapply Union_Disjoint_l; sets.
      
      normalize_sets.
      eapply cps_cvt_exp_fv in H.
      eapply Disjoint_Included_l.
      eapply Included_trans. eapply Setminus_Included. eassumption.
      eapply Union_Disjoint_l; sets.

      eapply Union_Disjoint_l. now sets.
      eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
      eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
      eassumption. (* TODO remove var *)
  Qed. 
      
     
      
  
  Lemma get_list_rev A xs (vs  : list A) rho :
    get_list xs rho = Some vs ->
    get_list (rev xs) rho = Some (rev vs).
  Proof.
    revert vs. induction xs; intros vs Hget; destruct vs; simpl in *; try congruence.
    - destruct (rho ! a); [ | congruence ].
      destruct (get_list xs rho); [ | congruence ]. inv Hget.
    - destruct (rho ! a) eqn:Hget'; [ | congruence ].
      destruct (get_list xs rho); [ | congruence ]. inv Hget.
      erewrite get_list_app. reflexivity. now eauto.
      simpl. rewrite Hget'. reflexivity. 
  Qed. 
  
  
    Lemma cps_env_rel_nth_error vnames vs rho n y v : 
      cps_env_rel vnames vs rho -> 
      nth_error vnames n = Some y ->
      nth_error vs n = Some v -> 
      exists v', M.get y rho = Some v' /\ cps_val_rel v v'.
    Proof.
      intros Hrel. revert n y v; induction Hrel; intros n z v Hnth1 Hnth2.
      - destruct n; simpl in *; congruence.
      - destruct n; simpl in *.
        + inv Hnth1. inv Hnth2. destructAll. eauto.
        + eauto.
    Qed. 

    Lemma preord_var_env_extend_neq_l PostG (rho1 rho2 : eval.env) (k : nat) (x1 y1 y2 : var)
          (v1 : cps.val) :
        preord_var_env cenv PostG k rho1 rho2 y1 y2 ->
        y1 <> x1 ->
        preord_var_env cenv PostG k (M.set x1 v1 rho1) rho2 y1 y2.
    Proof.
      intros Hval Hneq x' Hget.
      rewrite M.gso in *; eauto.
    Qed.

    Lemma preord_var_env_extend_neq_r PostG (rho1 rho2 : eval.env) (k : nat) (x1 y1 y2 : var)
          (v1 : cps.val) :
      preord_var_env cenv PostG k rho1 rho2 y1 y2 ->
      y2 <> x1 ->
      preord_var_env cenv PostG k rho1 (M.set x1 v1 rho2) y1 y2.
    Proof.
      intros Hval Hneq x' Hget.
      rewrite M.gso in *; eauto.
    Qed.

    Lemma preord_var_env_get :
      forall PostG (rho1 rho2 : eval.env) (k : nat) (x1 x2 : var) (v1 v2 : cps.val),
        preord_val cenv PostG k v1 v2 ->
        M.get x1 rho1 = Some v1 ->
        M.get x2 rho2 = Some v2 ->        
        preord_var_env cenv PostG k rho1 rho2 x1 x2.
    Proof.
      intros rho1 rho2 k x1 x2 v1 v2 Hval Hget1 Hget2 x' v' Hget.
      repeat subst_exp. eauto. 
    Qed.

    Lemma preord_var_env_get_list :
      forall PostG (rho1 rho2 : eval.env) (k : nat) (xs1 xs2 : list var) (vs1 vs2 : list cps.val),
        Forall2 (preord_val cenv PostG k) vs1 vs2 ->
        get_list xs1 rho1 = Some vs1 ->
        get_list xs2 rho2 = Some vs2 ->        
        Forall2 (preord_var_env cenv PostG k rho1 rho2) xs1 xs2.
    Proof.
      intros PG rho1 rho2 k xs1.
      revert rho1 rho2. induction xs1; intros rho1 rho2 xs2 vs1 vs2 Hall Hget1 Hget2.
      - simpl in Hget1. inv Hget1. inv Hall.
        destruct xs2. now constructor.
        simpl in *. destruct (rho2 ! v); try congruence.
        destruct (get_list xs2 rho2); congruence.
      - simpl in Hget1.
         destruct (rho1 ! a) eqn:Hget; try congruence.
         destruct (get_list xs1 rho1) eqn:Hgetl; try congruence.
         inv Hget1.
         inv Hall.
         destruct xs2. now inv Hget2. simpl in *.
         destruct (rho2 ! v0) eqn:Hget'; try congruence.
         destruct (get_list xs2 rho2) eqn:Hgetl'; try congruence.
         inv Hget2.
         constructor; eauto.

         eapply preord_var_env_get; eauto.
    Qed.

    

    Definition one_step : @PostT nat unit :=
      fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + 1)%nat = f2.


    Lemma preord_exp_Efun_red k e B rho :          
      preord_exp cenv one_step eq_fuel k (e, def_funs B B rho rho) (Efun B e, rho).
    Proof.
      intros r cin cout Hleq Hbstep.
      do 3 eexists. split. econstructor 2. econstructor. eassumption.
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Qed.

    Lemma preord_exp_Eapp_red k B rho f rho1 g xs ft ys e' vs rho2 :
      M.get f rho = Some (Vfun rho1 B g) ->
      find_def g B = Some (ft, ys, e') ->
      get_list xs rho = Some vs ->
      set_lists ys vs (def_funs B B rho1 rho1) = Some rho2 ->
      preord_exp cenv one_step eq_fuel k (e', rho2) (Eapp f ft xs , rho).
    Proof.
      intros r cin cout Hleq Hbstep Hget Hf Hgetl Hsetl.
      do 3 eexists. split. econstructor 2. econstructor; eauto. 
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Qed.


    Lemma preord_exp_Econstr_red k x ctag ys e rho vs :
      get_list ys rho = Some vs ->
      preord_exp cenv one_step eq_fuel k (e, M.set x (Vconstr ctag vs) rho) (Econstr x ctag ys e, rho).
    Proof.
      intros Hgvs r cin cout Hleq Hbstep.
      do 3 eexists. split. econstructor 2. econstructor; eauto. 
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Qed.

    
    Lemma eq_fuel_idemp : 
      inclusion _ (comp eq_fuel eq_fuel) eq_fuel.
    Proof.
      clear. unfold comp, eq_fuel. intro; intros. 
      destruct x as [[[? ?] ?] ?].
      destruct y as [[[? ?] ?] ?]. destructAll. 
      destruct x as [[[? ?] ?] ?]. congruence.
    Qed.
           
    (* TODO move *) 
    Ltac destruct_tuples :=
      try match goal with
          | [ X : ?A * ?B |- _ ] => destruct X; destruct_tuples
          end.

    
    Require Import set_util.


    Lemma MSet_non_member (s : PS.t) :
      exists x, ~ PS.In x s.
    Proof.
      destruct (PS.max_elt s) as [m | ] eqn:Hmax.
      - eexists (m + 1)%positive. 
        destruct (PS.mem (m + 1)%positive s) eqn:Hmem.
        + eapply PS.mem_spec in Hmem. eapply PS.max_elt_spec2 in Hmax; [ | eassumption ].
          exfalso. eapply Hmax. eapply Pos.compare_lt_iff. zify. lia.
        + intros Hc. eapply PS.mem_spec in Hc. congruence.
      - eapply PS.max_elt_spec3 in Hmax. eexists 1%positive.
        intros Hc. eapply Hmax. eassumption.
    Qed.

    Lemma ToMSet_non_member (S : Ensemble positive) {Hm: ToMSet S} :
      exists x, ~ x \in S.
    Proof.
      edestruct MSet_non_member. exists x. intros Hc.
      eapply H. eapply FromSet_sound. eapply Hm. eassumption.
    Qed.

    Lemma cps_env_rel_weaken vnames vs x v rho :
      cps_env_rel vnames vs rho ->
      ~ x \in FromList vnames ->
      cps_env_rel vnames vs (M.set x v rho).
    Proof.
      intros Henv Hnin. unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel' in *.
      eapply Forall2_monotonic_strong; [ | eassumption ].
      simpl. intros x1 x2 Hin1 Hin2 Hr. rewrite M.gso; eauto.
      intros Hc; subst; auto.
    Qed.


    Lemma cps_env_rel_weaken_setlists vnames vs xs vs' rho rho' :
      cps_env_rel vnames vs rho ->
      set_lists xs vs' rho = Some rho' ->
      Disjoint _ (FromList xs) (FromList vnames) ->
      cps_env_rel vnames vs rho'.
    Proof.
      revert vs' rho rho'; induction xs; intros vs1 rho1 rho2 Hrel Hset Hdis.
      - destruct vs1; inv Hset.  eassumption.
      - destruct vs1; inv Hset.
        destruct (set_lists xs vs1 rho1) eqn:Hset; inv H0.
        repeat normalize_sets. 
        eapply cps_env_rel_weaken.
        eapply IHxs. eassumption. eassumption.
        sets.
        intros Hc. eapply Hdis; eauto.
    Qed.
    

    Lemma cps_env_rel_extend vnames vs x v v' rho :
      cps_env_rel vnames vs rho ->
      M.get x rho = Some v' ->
      cps_val_rel v v' ->
      cps_env_rel (x :: vnames) (v :: vs) rho.
    Proof.
      intros Henv Hget Hval. unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel' in *.
      econstructor; eauto.
    Qed.

    
    Lemma cps_env_rel_extend_setlists vnames vs xs vs1 vs2 rho :
      cps_env_rel vnames vs rho ->
      get_list xs  rho = Some vs2 ->
      Forall2 (cps_val_rel) vs1 vs2 ->
      cps_env_rel (xs ++ vnames) (vs1 ++ vs) rho.
    Proof.
      revert vs1 vs2 rho; induction xs; intros vs1 vs2 rho1 Hrel Hset Hall.
      - simpl. inv Hset. inv Hall. eassumption.
      - simpl in Hset.
        destruct (rho1 ! a) eqn:Hget; try congruence.
        destruct (get_list xs rho1) eqn:Hgetl; try congruence. 
        inv Hset. inv Hall. simpl.
        eapply cps_env_rel_extend; eauto.
    Qed.


    Lemma cps_env_rel_extend_weaken vnames vs x v v' rho :
      cps_env_rel vnames vs rho ->
      cps_val_rel v v' ->
      ~ x \in FromList vnames ->
      cps_env_rel (x :: vnames) (v :: vs) (M.set x v' rho).
    Proof.
      intros Henv Hval Hnin. unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel' in *.
      econstructor; eauto.
      - rewrite M.gss. eexists. split; eauto.
      - eapply cps_env_rel_weaken; eauto.
    Qed.


    Lemma cps_env_rel_extend_weaken_setlists vnames vs xs vs1 vs2 rho rho' :
      cps_env_rel vnames vs rho ->
      set_lists xs vs2 rho = Some rho' ->
      Forall2 (cps_val_rel) vs1 vs2 ->
      Disjoint _ (FromList xs) (FromList vnames) ->
      NoDup xs ->
      cps_env_rel (xs ++ vnames) (vs1 ++ vs) rho'.
    Proof.
      intros.
      eapply cps_env_rel_extend_setlists; eauto.
      eapply cps_env_rel_weaken_setlists; eauto.
      eapply get_list_set_lists; eauto.
    Qed.


    Lemma nth_error_Forall2 (A B : Type) (P : A -> B -> Prop) (l : list A) (l' : list B) :
      (forall n t,
          nth_error l n = Some t ->
          exists t', nth_error l' n = Some t' /\ P t t') ->
      List.length l = List.length l' ->
      Forall2 P l l'.
    Proof.
      revert l'; induction l; intros l' Hyp Hlen.
      - destruct l'; simpl in *; try congruence. constructor.
      - destruct l'; simpl in *; try congruence. constructor.
        destruct (Hyp 0%nat a). reflexivity. destructAll. inv H. eassumption.

        eapply IHl; [ | congruence ].

        intros.
        
        destruct (Hyp (S n) t). eassumption. destructAll.
        eauto. 
    Qed.

    Lemma cps_cvt_rel_efnlst_all_fun_name S efns vs fnames S' fdefs :
      cps_cvt_rel_efnlst S efns vs fnames cnstrs S' fdefs ->
      all_fun_name fdefs = fnames. 
    Proof.
      intros Hefn. induction Hefn.
      - reflexivity.
      - simpl. congruence.
    Qed.
      
    Lemma cps_env_rel_extend_fundefs fnames names S1 fns Bs S2 rho vs :
      cps_env_rel names vs rho ->
      cps_fix_rel cnstrs func_tag kon_tag default_tag fnames names S1 fnames fns Bs S2 ->
      NoDup fnames ->
      NoDup names ->
      Disjoint var (FromList names :|: FromList fnames) S1 ->
      Disjoint var (FromList names) (FromList fnames) ->
      cps_env_rel (rev (all_fun_name Bs) ++ names) (make_rec_env_rev_order fns vs) (def_funs Bs Bs rho rho).
    Proof.
      intros Hrel Hfix Hnd1 Hnd2 Hdis1 Hdis2.
      unfold cps_env_rel, L4_to_L6_util.cps_env_rel, cps_env_rel'.
      destruct (make_rec_env_rev_order_app fns vs). destructAll. rewrite H.
      eapply Forall2_app.

      assert (Hlen : Datatypes.length x = Datatypes.length (all_fun_name Bs)).
      { erewrite cps_fix_rel_names; [ | eassumption ].
        rewrite H0. erewrite <- cps_fix_rel_length. reflexivity. eassumption. }

      - eapply nth_error_Forall2; [ | rewrite rev_length; eassumption ].
        intros.
        assert (exists f, nth_error (rev (all_fun_name Bs)) n = Some f).
        { eapply MCList.nth_error_Some_length in H2.
          rewrite Hlen, <- rev_length in H2. eapply nth_error_Some in H2.
          destruct (nth_error (rev (all_fun_name Bs)) n); eauto. congruence. }
        destructAll.
        eexists. split. eauto.
        eexists. split. rewrite def_funs_eq. reflexivity.
        eapply Same_set_all_fun_name. rewrite <- FromList_rev. eapply nth_error_In. eassumption.
        assert (Heq := H2). 
        rewrite H1 in Heq. 2:{ rewrite <- H0. eapply MCList.nth_error_Some_length. eassumption. }        
        inv Heq. econstructor; last eassumption; try eassumption.
        eapply cps_fix_rel_names in Hfix. rewrite <- Hfix.
        rewrite MCList.nth_error_rev.

        rewrite Nnat.Nat2N.id.
        replace (Datatypes.length (all_fun_name Bs) - S (efnlength fns - n - 1))%nat with n.
        2:{ rewrite <- H0, <- Hlen. eapply MCList.nth_error_Some_length in H2. lia. }
        eassumption.

        rewrite Nnat.Nat2N.id. rewrite <- H0, Hlen.
        destruct (all_fun_name Bs). now destruct n; inv H3.
        simpl. destruct n; lia.

      - eapply Forall2_monotonic_strong; [ | eassumption ].
        intros. rewrite def_funs_neq. eassumption.
        intros Hc. eapply Hdis2. constructor. eassumption.
        eapply cps_fix_rel_names in Hfix. rewrite <- Hfix.
        eapply Same_set_all_fun_name. eassumption.
    Qed.


    Lemma cps_val_rel_exists_list vs1 :
      Forall (well_formed_val) vs1 ->
      exists vs2, Forall2 (cps_val_rel) vs1 vs2.
    Proof.
      intros Hall; induction Hall.
      - eexists. constructor.
      - destructAll.
        edestruct cps_val_rel_exists.
        exact (M.empty _). (* TODO remove arg *)
        eassumption.
        eexists. constructor. eauto. eassumption.
    Qed.


    Lemma exps_wf_app es es1 es2 n :
      exps_to_list es = exps_to_list es1 ++ exps_to_list es2 ->
      exps_wf n es ->
      exps_wf n es1 /\ exps_wf n es2. 
    Proof.
      revert es1 es2; induction es; intros es1 es2 Heq Hwf.
      + destruct es1; destruct es2; simpl in *; try congruence.
        split; constructor. 
      + destruct es1; simpl in *; try congruence; inv Heq; inv Hwf.
        * destruct es2; inv H0.
          
          edestruct IHes with (es1 := enil). split. eassumption.
          split. 
          constructor. constructor; eauto. 
          eapply exps_to_list_inj in H2. subst; eauto.

        * edestruct IHes with (es1 := es1) (es2 := es2). eassumption.
          eassumption. split.
          constructor. eassumption. eassumption. eassumption.
    Qed.


    Context
      (dcon_to_tag_inj :
         forall tgm dc dc',
           dcon_to_tag default_tag dc tgm = dcon_to_tag default_tag dc' tgm -> dc = dc').    
    
    Lemma cps_cvt_rel_branches_find_branch S1 brs vs k r S2 P dc e tg n :
      cps_cvt_rel_branches S1 brs vs k r cnstrs S2 P ->
      find_branch dc n brs = Some e ->
      tg = dcon_to_tag default_tag dc cnstrs ->
       exists vars S1' S2' ce ctx_p m,
         FromList vars \subset S1 /\
         List.length vars = N.to_nat n /\
         S1' \subset S1 \\ FromList vars /\
         NoDup vars /\
         ctx_bind_proj tg r vars (List.length vars) = ctx_p /\
         find_tag_nth P tg (ctx_p |[ ce ]|) m /\
         L4_to_L6.cps_cvt_rel func_tag kon_tag default_tag S1' e 
                              (vars ++ vs) k cnstrs S2' ce. 
    Proof.
      intros Hrel Hf Htg.
      induction Hrel.
      - inv Hf.
      - unfold find_branch in Hf. destruct (classes.eq_dec dc dc0); subst.
        + simpl in *.
          destruct (N.eq_dec n0 n); try congruence.
          inv Hf.
          do 6 eexists.
          split; [ | split ; [ | split ; [ | split; [ | split ; [ | split ] ] ] ] ]; try eassumption.
          * eapply Included_trans. eassumption.
            eapply cps_cvt_branches_subset. eassumption.
          * eapply Included_Setminus_compat; sets.
            eapply cps_cvt_branches_subset. eassumption. 
          * now sets. 
          * simpl. rewrite <- H2.  eapply find_tag_hd.
        + edestruct IHHrel. eassumption. reflexivity. destructAll.
          do 6 eexists.
          split; [ | split ; [ | split ; [ | split; [ | split ; [ | split ] ] ] ] ]; last eassumption; try eassumption.
          * reflexivity.
          * constructor. eassumption.
            intros Hc. eapply dcon_to_tag_inj in Hc. subst; eauto.
    Qed.

    
    Lemma eval_fuel_many_length vs es vs1 f1 :
      eval_fuel_many vs es vs1 f1 ->
      List.length vs1 = N.to_nat (exps_length es).
    Proof.
      intros Hrel.
      induction Hrel.
      reflexivity.
      simpl. rewrite IHHrel.
      destruct (exps_length es); try lia.
      destruct p; lia.
    Qed.

    Lemma preord_exp_Eproj_red k x ctag y N e vs v rho :
      M.get y rho = Some (Vconstr ctag vs) ->
      nthN vs N = Some v ->
      preord_exp cenv one_step eq_fuel k (e, M.set x v rho) (Eproj x ctag N y e, rho).
    Proof.
      intros Hget Hnth r c1 c2 Hleq Hstep.
      do 3 eexists. split. econstructor 2. econstructor; eauto. 
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Qed.


    Lemma preord_exp_Ecase_red k rho ctag vs P e n y :
      M.get y rho = Some (Vconstr ctag vs) ->
      find_tag_nth P ctag e n ->
      preord_exp cenv one_step eq_fuel k (e, rho) (Ecase y P, rho).
    Proof.
      intros Hget Hnth r c1 c2 Hleq Hstep.
      do 3 eexists. split. econstructor 2. econstructor; eauto.
      admit. (* case consistent??? *) 
      split. simpl. unfold_all. lia. 
      eapply preord_res_refl; tci.
    Admitted.


    Definition eq_fuel_n (n : nat) : @PostT nat unit :=
      fun '(e1, r1, f1, t1) '(e2, r2, f2, t2) => (f1 + n)%nat = f2.


    Opaque preord_exp'.

    Lemma ctx_bind_proj_preord_exp :
      forall vars C k r n e rho rho' vs vs'  ctag,
        n = (List.length vars) ->
        ~ r \in FromList vars ->
        ctx_bind_proj ctag r vars n = C ->
        M.get r rho = Some (Vconstr ctag (vs ++ vs')) ->    
        set_lists (rev vars) vs rho = Some rho' ->
        preord_exp cenv (eq_fuel_n n) eq_fuel k (e, rho') (C |[ e ]|, rho).
    Proof.
      induction vars; intros C k r n e rho rho' vs vs' ctag Heq Hnin Hctx Hget Hset.
      - destruct vs. 2:{ simpl in Hset. destruct (rev vs); inv Hset. }
        simpl in Hset. inv Hset.
        simpl.
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_refl. tci. eapply preord_env_P_refl. tci. }

        unfold eq_fuel, eq_fuel_n. intro; intros. destruct_tuples. lia.

      - destruct n; inv Heq.
        simpl in *. 
        revert vs Hget Hset.
        intros vs. eapply MCList.rev_ind with (l := vs); intros.

        + eapply set_lists_length_eq in Hset.
          rewrite app_length in Hset. inv Hset. lia.
          
        + simpl in Hset.

          assert (Hlen : Datatypes.length (rev vars) = Datatypes.length l). 
          { eapply set_lists_length_eq in Hset. rewrite !app_length in Hset. simpl in *.
            replace (@Datatypes.length map_util.M.elt) with (@Datatypes.length positive) in * by reflexivity.
            lia. } 

          edestruct (@set_lists_app val). eassumption. eassumption.

          destructAll. inv H0.

          (* rewrite rev_unit in *. *)
          (* destruct (set_lists vars (rev l) rho) eqn:Hset'; inv Hset. *)
          (* simpl. *)

          (* edestruct (set_lists_length3 (M.set a x rho) vars (rev l)). *)
                  
          (* eapply set_lists_length_eq. eassumption. *)
          
          eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros m. eapply preord_exp_Eproj_red. eassumption.
                  eapply nthN_is_Some_app. 
                  eapply set_lists_length_eq in Hset.
                  rewrite rev_length in *.
                  replace (@Datatypes.length map_util.M.elt) with (@Datatypes.length positive) in * by reflexivity.
                  rewrite Hlen. rewrite nthN_app_geq. simpl.
                  
                  replace (N.of_nat (Datatypes.length l - 0) - N.of_nat (Datatypes.length l)) with 0 by lia.
                  reflexivity.
                  lia. }

              repeat normalize_sets.

              eapply IHvars with (vs := l). reflexivity. eauto.
              
              rewrite <- minus_n_O. reflexivity.
              
              rewrite M.gso; eauto. 
              
              rewrite app_assoc. eassumption.
              
              now intros Hc; subst; eauto. eassumption. }
              
          { unfold comp, eq_fuel_n, eq_fuel. intro; intros. destructAll. destruct_tuples.
            unfold one_step in *. lia. }

    Qed.
    
                                               
    Ltac inv_setminus :=
      match goal with
      | [ H : In _ (?S \\ ?Q) _ |- _ ] => inv H; try inv_setminus
      end.
    
    Lemma cps_cvt_correct : forall vs e r f, eval_env_fuel vs e r f -> cps_cvt_correct_exp vs e r f.
    Proof.
      eapply eval_env_fuel_ind' with (P1 := cps_cvt_correct_exp)
                                     (P0 := cps_cvt_correct_exps)
                                     (P := cps_cvt_correct_exp_step).
      
      - (* Con_e terminates *)
        intros es vs1 vs dc f1 Heval IH.
        intros rho vnames k x vk e' S S' i Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps. split; [ | congruence ]. 
        
        intros v1 v2 Heq Hrel. inv Heq. inv Hrel. 
                
        eapply preord_exp_post_monotonic.
        
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
            
            2:{ intros m. eapply preord_exp_Efun_red. } 
            
            set (rho' := M.set k1
                               (Vfun rho
                                     (Fcons k1 kon_tag vx
                                            (Econstr x1 (dcon_to_tag default_tag dc cnstrs) vx (Eapp k kon_tag [x1])) Fnil)
                                     k1) rho).
            
            edestruct IH with (ys := @nil var) (vs' := @nil val) (rho := rho'); [ | | | | | | | | | eassumption | eassumption | | ]. 
            - eassumption.
            - eassumption.
            - repeat normalize_sets. eapply Union_Disjoint_l; xsets.
            - repeat normalize_sets.
              eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
              eapply Union_Included; eapply Included_trans; eauto; sets.
            - repeat normalize_sets.
              eapply Disjoint_Included_l; eauto; sets.
            - repeat normalize_sets; sets.
            - eassumption.              
            - unfold rho'. eapply cps_env_rel_weaken. eassumption.
              intros Hc. inv_setminus. eapply Hdis; eauto.
            - normalize_occurs_free.
              eapply Union_Disjoint_l.
              now eapply Disjoint_Included_r; eauto; sets.
              now eapply Disjoint_Included_r; eauto; sets.
            - reflexivity.
            - destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply H0. } 


              edestruct (set_lists_length3 rho' vx vs').
              { replace (@Datatypes.length map_util.M.elt) with (@Datatypes.length var) in * by reflexivity.
                rewrite H8. eapply Forall2_length in H2. rewrite <- H2.
                erewrite <- eval_fuel_many_length. reflexivity. eassumption. }
              
              simpl in *.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. simpl. eapply preord_exp_Eapp_red.
                  - erewrite <- set_lists_not_In; [ | eassumption | ].
                    unfold rho'. rewrite M.gss. reflexivity.
                    simpl. intros Hc. eapply H6 in Hc. inv_setminus; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. eapply get_list_set_lists; eassumption.
                  - simpl. eassumption. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Econstr_red.
                  eapply get_list_set_lists. eassumption.
                  eassumption. }

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_get.
              2:{ eapply M.gss. }
              2:{ erewrite <- set_lists_not_In; [ | eassumption | ].
                  unfold rho'. rewrite M.gso. eassumption.
                  intros Hc; subst. inv H4. now eapply Hdis; eauto.
                  intros Hc. eapply H5 in Hc. inv_setminus. eapply Hdis; eauto. }
              
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              intros Hc; subst; eapply Hdis; now eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
        
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. }

      - (* Con_e OOT *)
        intros es es1 es2 e vs1 vs dc f1 fs Heq Heval IH Hoot IHoot.
        intros rho vnames k x vk e' S S' i Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps. split. congruence.
        
        intros _.

        edestruct cps_cvt_rel_exps_app with (es2 := econs e es2). eassumption. eassumption.
        destructAll.

        assert (Hex :  exists vs2, Forall2 (cps_val_rel) vs1 vs2).
        { eapply cps_val_rel_exists_list.         
          admit. } destructAll.


        set (rho' := M.set k1
                           (Vfun rho
                                 (Fcons k1 kon_tag vx
                                        (Econstr x1 (dcon_to_tag default_tag dc cnstrs) vx (Eapp k kon_tag [x1])) Fnil)
                                 k1) rho).


        unfold cps_cvt_correct_exps in *.
        eapply IH with (rho := rho') (ys := []) (vs' := []) in H13; clear IH; [ | | | | | | | | | | eassumption | reflexivity ]; eauto.
        + destructAll.

          inv H11.

          assert (Hex' : exists z, ~ In var (k0 |: FromList vnames) z).
          { eapply ToMSet_non_member. tci. } destructAll.

          set (rho'' := M.set k0 (Vfun x8 (Fcons k0 kon_tag [x9] es' Fnil) k0) x8).
          eapply IHoot with (rho := rho'') in H17.

          * destructAll.
            assert (Hoot' : bstep_fuel cenv x8 (Efun (Fcons k0 kon_tag [x9] es' Fnil) e') (x4 + 1)%nat OOT tt).
            { replace tt with (tt <+> tt) by reflexivity. econstructor 2. econstructor. simpl. eassumption. }
            
            edestruct H13. reflexivity. eassumption. destructAll.
            eexists. split.
            2:{ replace tt with (tt <+> tt). econstructor 2. econstructor. simpl.
                destruct x6; [ | contradiction ]. destruct x11. eassumption.
                reflexivity. }
            
            simpl. unfold cps_bound, one, fuel_sem.one in *; simpl; unfold_all. lia.
            
          * eassumption.
          * eassumption.
          * admit. (* exps wf list lemma  easy wf *)
          * eapply Disjoint_Included_r. eassumption.
            eapply Union_Disjoint_l.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
            xsets. 
          * eassumption.
          * intros Hc. eapply Hdis. constructor. now right.
            eapply H7.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
          * unfold rho'. eapply cps_env_rel_weaken.
            simpl in *.
            eapply cps_env_rel_weaken_setlists; [ | eauto | ].
            repeat eapply cps_env_rel_weaken. eassumption.
            intros Hc. inv_setminus. eapply Hdis. now eauto.
            eapply Disjoint_sym. eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
            eapply Included_trans.
            eapply Included_trans; [ | eapply H6 ].
            repeat rewrite FromList_app, FromList_cons at 1. now sets. now sets.
            intros Hc.
            eapply Hdis. constructor. now right.
            eapply H7.
            repeat rewrite FromList_app, FromList_cons at 1. now sets.
          * unfold rho''. rewrite M.gss. reflexivity.
          * reflexivity.

        + admit. (* wf _lemma *) 
        + repeat rewrite FromList_app; rewrite FromList_nil.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
          eapply Union_Disjoint_l; sets.
          xsets. 
        + eapply Disjoint_Included; [ | | eapply Hdis ]; sets. do 2 normalize_sets.  
          eapply Union_Included. 

          eapply Included_trans.
          eapply Included_trans; [ | eapply H6 ].
          repeat rewrite FromList_app.  now sets. now sets. 

          
          eapply Included_trans.
          eapply Included_trans; [ | eapply H7 ].
          repeat rewrite FromList_app.  now sets. now sets.

        + eapply Disjoint_Union_l.
          rewrite <- FromList_app. eapply Disjoint_Included_l. eassumption.
          rewrite FromList_app, FromList_nil. sets.

        + normalize_sets. sets.
        + eapply NoDup_cons_l. eassumption.
        + unfold rho'. eapply cps_env_rel_weaken. eassumption.
          intros Hc. inv_setminus. eapply Hdis; eauto.

        + admit.
          
      - (* App_e Clos_v *) 
        intros e1 e2 e1' v2 r' na vs vs' f1 f2 f3  Heval1 IH1 Heval2 IH2 Heval3 IH3.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.
        inv Hwf. inv Hcps.

        assert (Hlen : Datatypes.length vs = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }

        assert (Hwfv2 : well_formed_val v2).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. } 
        
        assert (Hwfcl : well_formed_val (Clos_v vs' na e1')).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }
        
        assert (Hex : exists v', cps_val_rel (Clos_v vs' na e1') v').
        { eapply cps_val_rel_exists. eassumption. eassumption. }
        
        assert (Hex' : exists v', cps_val_rel v2 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } 
        
        destructAll. inv H0.
        
        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *) 
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+> f2 <+> fuel_sem.one (e1 $ e2))) eq_fuel m
                                            (e', M.set k0 vk (M.set x4 x0 (M.set f0 (Vfun rho0 (Fcons f0 func_tag [k0; x4] e' Fnil) f0) rho0)))
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1'0, rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | | |  eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption. 
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - intros Hc. inv_setminus. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv_setminus. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - econstructor; eauto. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } simpl.
              
              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              assert (HS2 := H8). eapply cps_cvt_rel_subset in HS2.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

              
              2:{ intros m. simpl. eapply IH2 ; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - eassumption.
                  - eassumption. 
                  - eapply Disjoint_Included_r. eassumption. 
                    eapply Union_Disjoint_l; sets.
                    eapply Setminus_Disjoint_preserv_r.
                    eapply Disjoint_Included ; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - inv_setminus. intros Hin. eapply Hdis. eauto.
                  - repeat eapply cps_env_rel_weaken. eassumption.
                    inv_setminus. intros Hc. now eapply Hdis; eauto.
                    intros Hc. now eapply Hdis; eauto.
                    inv_setminus. intros Hin. eapply Hdis. eauto.
                  - rewrite M.gss. reflexivity. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              (* inv H0. simpl. *)
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gso; eauto.
                rewrite M.gss. reflexivity.
                intros Hc; subst. now inv_setminus; eauto.
                intros Hc; subst. now inv_setminus; eauto.
              - simpl. rewrite Coqlib.peq_true. reflexivity.
              - simpl. rewrite M.gso.
                simpl. rewrite M.gso.                    
                simpl. rewrite M.gso.
                simpl. rewrite M.gso. rewrite M.gss.
                rewrite Hget. reflexivity.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
                intros Hc; subst. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
              - simpl. reflexivity. } 

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        split.

        (* Termination *) 
        { intros v v' Heq1 Hvrel. subst. 

          assert (Hex : exists x, ~ In var (k0 |: FromList (x4 :: names)) x).
          { eapply ToMSet_non_member. tci. } destructAll. 
          
          eapply preord_exp_post_monotonic.
          
          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp. 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH3 with (x := x3); [ | | | | | | | eassumption | reflexivity  | eapply Hvrel ].
                  - inv Hwfcl. constructor; eauto.
                  - inv Hwfcl. specialize (H20 v). simpl Datatypes.length in *.
                    erewrite <- Forall2_length. eassumption. eassumption. 
                  - repeat normalize_sets. sets.
                  - eassumption.
                  - repeat normalize_sets. inv_setminus. intros Hc. inv Hc; eauto. inv H4; eauto.
                  - eapply cps_env_rel_weaken; eauto.
                    eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto.
                    repeat normalize_sets. intros Hc. inv Hc; eauto. inv H7; eauto.
                  - rewrite M.gss. reflexivity. } 
              
              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 
          
        (* OOT *)
        { intros ?; subst.
          assert (Hex : exists x, ~ In var (k0 |: FromList (x4 :: names)) x).
          { eapply ToMSet_non_member. tci. } destructAll. 

          edestruct IH3 with (x := x3) (rho :=  M.set k0 vk (M.set x4 x0 (M.set f0 (Vfun rho0 (Fcons f0 func_tag [k0; x4] e' Fnil) f0) rho0)));
            [ | | | | | | | eassumption | ].
          - inv Hwfcl. constructor; eauto.
          - inv Hwfcl. specialize (H20 v2). simpl Datatypes.length in *.
            erewrite <- Forall2_length. eassumption. eassumption. 
          - repeat normalize_sets. sets.
          - eassumption.
          - repeat normalize_sets. sets.
            intros Hc; inv Hc; eauto. inv H7; eauto. 
          - eapply cps_env_rel_weaken; eauto.
            eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto.
            repeat normalize_sets. intros Hc; inv Hc. inv H7; eauto. eapply H16; eauto. 
          - rewrite M.gss. reflexivity.
          - destruct (H9 ltac:(reflexivity)). destructAll. eapply Heq in H17; [ | reflexivity ]. destructAll.
            destruct x6; try contradiction. destruct x8. eexists. split; [ | eassumption ].
            
            unfold fuel_sem.one in *. simpl in *. lia. } 

      - (* App_e Clos_v, OOT 1 *)
        intros e1 e2 vs f1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split. 
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho
                                    (Fcons k1 kon_tag [x1]
                                           (Efun
                                              (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil)
                                              e2') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 
        
        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + eapply Union_Disjoint_l; sets.
          eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
        + eassumption.
        + intros Hc; inv H2; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros Hc. inv H2. eapply Hdis; eauto. 
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H5. reflexivity. destructAll. eexists (x3 + 1)%nat. split.
          unfold fuel_sem.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.
          
      - (* App_e Clos_v, OOT 2 *)
        intros e1 e2 v1 vs2 f1 f2 He1 IH1 Hoot IH2.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        
        assert (Hlen : Datatypes.length vs2 = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }
        
        assert (Hwfv2 : well_formed_val v1).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. } 

        assert (Hex' : exists v', cps_val_rel v1 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } destructAll. 

        set (rho' := M.set k2 (Vfun (M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) k1) rho)) (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) k2)
                           (M.set x1 x0
                                  (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1]
                                                             (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2])
                                                                          Fnil) e2') Fnil) k1) rho))).
        
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+>fuel_sem.one (e1 $ e2))) eq_fuel m
                                            (e2', rho')
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1', rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - eassumption. }
          
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }  
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
               
              2:{ intros m. eapply preord_exp_Efun_red. } simpl. 

              eapply preord_exp_refl. tci.
              eapply preord_env_P_refl. tci. }
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        
        assert (Hex : exists x, ~ In var (k2 |: FromList (vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2. 
        
        edestruct IH2 with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption. 
        + repeat normalize_sets.
          eapply Disjoint_Included_r. eassumption.
          eapply Union_Disjoint_l; sets.
          repeat eapply Setminus_Disjoint_preserv_r. sets.
        + eassumption.
        + inv_setminus. intros Hc; eauto. eapply Hdis; eauto.
        + inv_setminus.
          repeat eapply cps_env_rel_weaken; eauto; now intros Hc; eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct (H9 ltac:(reflexivity)). destructAll. eapply Heq in H11; [ | reflexivity ]. destructAll.
          destruct x5; try contradiction. destruct x7. eexists. split; [ | eassumption ].
          unfold fuel_sem.one in *. simpl in *. lia.

      - (* Let_e *)
        intros e1 e2 v1 r vs na f1 f2 He1 IH1 He2 IH2.
        intros rho vnames k x vk e' S S' f Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. inv Hcps. inv Hwf.


        assert (Hlen : Datatypes.length vs = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }
        
        assert (Hwfv2 : well_formed_val v1).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. } 

        assert (Hex' : exists v', cps_val_rel v1 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } destructAll. 
        
        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *) 
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+> fuel_sem.one (Let_e na e1 e2))) eq_fuel m
                                            (e2', map_util.M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho))
                                            (Efun (Fcons k1 kon_tag [x1] e2' Fnil) e1', rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption. 
                  - eapply Disjoint_Included_r. eapply cps_cvt_exp_subset. eassumption.
                    eapply Union_Disjoint_l; sets.
                  - eassumption.
                  - intros Hc. inv H4. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken; try eassumption.
                    intros Hc. inv H4. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - eassumption. }
              
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
              - simpl. rewrite Coqlib.peq_true. reflexivity.
              - simpl. rewrite M.gss. reflexivity.
              - simpl. reflexivity. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } } 

        assert (Hex : exists x, ~ In var (k |: FromList (x1 :: vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.
        
        split. 
        (* Termination *) 
        { intros v v' Heq1 Hvrel. subst. 
          
          eapply preord_exp_post_monotonic.
          
          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp. 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH2; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - constructor; eauto.
                  - simpl Datatypes.length. rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l. eassumption. 
                  - repeat normalize_sets. eapply Union_Disjoint_l; sets.
                    eapply Union_Disjoint_l; sets.                    
                  - eassumption.
                  - repeat normalize_sets. intros Hc; inv Hc; eauto. inv H1.
                    eapply Hdis. eauto.
                  - eapply cps_env_rel_extend_weaken; eauto.
                    eapply cps_env_rel_weaken; eauto.
                    intros Hc. inv H4. eapply Hdis; eauto.
                    intros Hc. eapply Hdis; eauto.
                  - rewrite !M.gso. eassumption.
                    intros Hc; subst; inv H4; eapply Hdis; eauto.
                    intros Hc; subst; inv H4; eapply Hdis; eauto. } 

              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 
        
        (* OOT *)
        { intros ?; subst.

          edestruct IH2 with (x := x2) (rho := M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho));
            [ | | | | | | | eassumption | ].
          - constructor; eauto.
          - simpl Datatypes.length. rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l. eassumption. 
          - repeat normalize_sets.
            eapply Union_Disjoint_l; sets.
            eapply Union_Disjoint_l; sets.
          - eassumption.
          - repeat normalize_sets. sets.
            intros Hc; inv Hc; eauto. inv H1. eapply Hdis; eauto. 
          - eapply cps_env_rel_extend_weaken; eauto.
            eapply cps_env_rel_weaken; eauto.
            intros Hc. inv H4; eapply Hdis; eauto.
            intros Hc. inv H4; eapply Hdis; eauto.
          - rewrite !M.gso. eassumption.
            (* TODO tactic to do these + hint constructor *)
            intros Hc; subst; inv H4; eapply Hdis; eauto.
            intros Hc; subst; inv H4; eapply Hdis; eauto.
          - destruct (H5 ltac:(reflexivity)). destructAll. eapply Heq in H8; [ | reflexivity ]. destructAll.
            destruct x4; try contradiction. destruct x6. eexists. split; [ | eassumption ].
            
            unfold fuel_sem.one in *. simpl in *. lia. } 
        
      - (* Let_e, OOT *)
        intros e1 e2 vs na f1 Hoot IH. 
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] e2' Fnil) k1) rho).

        assert (HS2 := H10). eapply cps_cvt_rel_subset in HS2. 

        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 

        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + inv H4. eapply Disjoint_Included_r. eassumption. sets.
          eapply Union_Disjoint_l; sets.
        + eassumption.
        + intros Hc; inv H4; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros Hc. inv H4. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H1. reflexivity. destructAll. eexists (x2 + 1)%nat. split.
          unfold fuel_sem.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor; eauto.

      - (* App_e, ClosFix_v *)
        intros e1 e2 e1' vs1 vs2 vs3 n na fns v2 r f1 f2 f3  Heval1 IH1 Hnth Hrec Heval2 IH2 Heval3 IH3.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps.  
        inv Hcps.  inv Hwf.

        assert (Hlen : Datatypes.length vs1 = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }

        assert (Hwfv2 : well_formed_val v2).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. } 
        
        assert (Hwfcl : well_formed_val (ClosFix_v vs2 fns n)).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. }
        
        assert (Hex : exists v', cps_val_rel (ClosFix_v vs2 fns n) v').
        { eapply cps_val_rel_exists. eassumption. eassumption. }
        
        assert (Hex' : exists v', cps_val_rel v2 v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } 

        destructAll. inv H0.
        
        edestruct L4_to_L6_util.cps_fix_rel_exists. eassumption. eassumption. eassumption. 
        destruct H0 as (y1 & na' & e3 & e3' & Hu). destructAll.  
        repeat subst_exp. 
        (* Prove that whole CPS-term is related to the body of the app -- useful for both cases *) 
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+> f2 <+> fuel_sem.one (e1 $ e2))) eq_fuel m
                                            (e3', (map_util.M.set x3 vk (map_util.M.set y1 x0 (def_funs Bs Bs rho0 rho0))))
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) e1'0,
                                             rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption. 
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; now sets. 
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken; try eassumption.
                    intros Hc. inv H2; eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity.
                  - econstructor; eauto. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } simpl.
              
              assert (Hex' : exists z, ~ In var (k2 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2.              
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

              
              2:{ intros m. simpl. eapply IH2 ; [ | | | | | | | eassumption | reflexivity | eassumption ].
                  - eassumption.
                  - eassumption. 
                  - eapply Disjoint_Included_r. eassumption. 
                    eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - inv_setminus. intros Hin. eapply Hdis. eauto.
                  - repeat eapply cps_env_rel_weaken. eassumption.
                    intros Hc. inv H2. now eapply Hdis; eauto.
                    intros Hc. now eapply Hdis; eauto.
                    inv_setminus. intros Hin. eapply Hdis. eauto.
                  - rewrite M.gss. reflexivity. } 
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 
              
              (* inv H0. simpl. *)
              eapply preord_exp_Eapp_red.
              - rewrite M.gso; eauto. rewrite M.gso; eauto.
                rewrite M.gss. reflexivity.
                inv_setminus. intros Hin. subst; eauto.
                inv_setminus. intros Hin. subst; eauto.
              - eassumption. 
              - simpl. rewrite M.gso.
                simpl. rewrite M.gso.                    
                simpl. rewrite M.gso.
                simpl. rewrite M.gso. rewrite M.gss.
                rewrite Hget. reflexivity.
                intros Hc; subst. inv H2. now eapply Hdis; eauto.
                intros Hc; subst. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
                intros Hc; subst. inv_setminus. now eapply Hdis; eauto.
              - simpl. reflexivity. } 

          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        split. 

        (* Termination *)  
        { intros v v' Heq1 Hvrel. subst. 

          assert (Hex : exists x, ~ In var (x3 |: FromList (y1 :: fnames ++ names)) x).
          { eapply ToMSet_non_member. tci. } destructAll.
          
          eapply preord_exp_post_monotonic.
          
          2:{ eapply preord_exp_trans; [ | | | eassumption ]. tci. eapply eq_fuel_idemp. 

              repeat subst_exp.
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH3; [ | | | | | | | eassumption | reflexivity  | eapply Hvrel ].
                  - inv Hwfcl. constructor; eauto.
                    eapply well_formed_envmake_rec_env_rev_order. reflexivity. eassumption. eassumption.
                  - inv Hwfcl.
                    eapply enthopt_inlist_Forall in H26; [ | eassumption ].
                    inv H26. inv H22. simpl Datatypes.length.
                    rewrite app_length, rev_length. erewrite cps_fix_rel_length; [ | eassumption ].
                    erewrite <- Forall2_length; [ | eassumption ].
                    rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l, Nnat.Nat2N.inj_add, efnlength_efnlst_length.
                    eassumption.
                  - repeat normalize_sets.
                    eapply Union_Disjoint_l; sets.
                    eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Singleton_l. now eauto.
                    eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets. 
                  - repeat normalize_sets. rewrite FromList_rev. eassumption.
                  - repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto. inv H21; eauto.
                  - eapply cps_env_rel_weaken; eauto.
                    eapply cps_env_rel_extend_weaken; eauto.
                    erewrite <- cps_fix_rel_names with (fnames' := fnames); [ | eassumption ].
                    eapply cps_env_rel_extend_fundefs; try eassumption.
                    repeat normalize_sets. rewrite FromList_rev. now eauto.
                    repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto.
                    inv H21; eauto.
                  - rewrite M.gss. reflexivity. } 
              
              eapply preord_exp_app_compat with (P2 := eq_fuel).
              now eapply eq_fuel_compat. 
              now eapply eq_fuel_compat. 
              
              eapply preord_var_env_extend_neq. 
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. 
              now intros Hc; subst; eauto.
              now intros Hc; subst; eauto.
              constructor.
              eapply preord_var_env_extend_eq.
              eapply preord_val_refl. now tci. now constructor. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 
        
        (* OOT *)
        { intros ?; subst.
          assert (Hex : exists x, ~ In var (x3 |: FromList (y1 :: fnames ++ names)) x).
          { eapply ToMSet_non_member. tci. } destructAll. 

          edestruct IH3 with (rho := M.set x3 vk (map_util.M.set y1 x0 (def_funs Bs Bs rho0 rho0)));
            [ | | | | | | | eassumption | ].
          - inv Hwfcl. constructor; eauto.
            eapply well_formed_envmake_rec_env_rev_order. reflexivity. eassumption. eassumption.
          - inv Hwfcl.
            eapply enthopt_inlist_Forall in H26; [ | eassumption ].
            inv H26. inv H22. simpl Datatypes.length.
            rewrite app_length, rev_length. erewrite cps_fix_rel_length; [ | eassumption ].
            erewrite <- Forall2_length; [ | eassumption ].
            rewrite Nnat.Nat2N.inj_succ, <- OrdersEx.N_as_OT.add_1_l, Nnat.Nat2N.inj_add, efnlength_efnlst_length.
            eassumption.
          - repeat normalize_sets.
            eapply Union_Disjoint_l; sets.
            eapply Union_Disjoint_l; sets.
            eapply Disjoint_Singleton_l. now eauto.
            eapply Disjoint_Included_r. eassumption. rewrite FromList_rev. sets.
          - repeat normalize_sets. rewrite FromList_rev. eassumption.
          - repeat normalize_sets. rewrite FromList_rev. sets.
            intros Hc; inv Hc; eauto. inv H21; eauto.
          - eapply cps_env_rel_weaken; eauto.
            eapply cps_env_rel_extend_weaken; eauto.
            erewrite <- cps_fix_rel_names with (fnames' := fnames); [ | eassumption ].
            eapply cps_env_rel_extend_fundefs; try eassumption.
            repeat normalize_sets. rewrite FromList_rev. now eauto.
            repeat normalize_sets. rewrite FromList_rev. intros Hc; inv Hc; eauto.
            inv H21; eauto.
          - rewrite M.gss. reflexivity.
          - destruct (H22 ltac:(reflexivity)). destructAll. eapply Heq in H24; [ | reflexivity ]. destructAll.
            destruct x8; try contradiction. destruct x10. eexists. split; [ | eassumption ].
            
            unfold fuel_sem.one in *. simpl in *. lia. } 
        

      - (* App_e, ClosFix_v, OOT 1 *)
        intros e1 e2 vs f1 Hoot IH.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho
                                    (Fcons k1 kon_tag [x1]
                                           (Efun
                                              (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil)
                                              e2') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 
        
        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.          
        + eapply Union_Disjoint_l; sets.
          eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
        + eassumption.
        + intros Hc; inv H2; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          inv H2. intros Hc. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct H5. reflexivity. destructAll. eexists (x3 + 1)%nat. split.
          unfold fuel_sem.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.
          
      - (* App_e, ClosFix_v, OOT 2 *)
        intros e1 e2 v vs f1 f2 He1 IH1 Hoot IH2.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hget Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.

        assert (Hlen : Datatypes.length vs = Datatypes.length vnames).
        { unfold well_formed_in_env. eapply Forall2_length. eassumption. }
        
        assert (Hwfv2 : well_formed_val v).
        { eapply eval_env_step_preserves_wf; [ | reflexivity | | ]. eassumption.
          eassumption. unfold well_formed_in_env. rewrite Hlen. eassumption. } 
                
        assert (Hex' : exists v', cps_val_rel v v').
        { eapply cps_val_rel_exists. eassumption. (* TODO remove arg *) eassumption. } 
        destructAll.

        set (rho' := M.set k2 (Vfun (M.set x1 x0 (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil) k1) rho)) (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) k2)
                           (M.set x1 x0
                                  (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1]
                                                             (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2])
                                                                          Fnil) e2') Fnil) k1) rho))).
        
        assert (Heq : forall m, preord_exp' cenv (preord_val cenv) (cps_bound (f1 <+>fuel_sem.one (e1 $ e2))) eq_fuel m
                                            (e2', rho')
                                            (Efun (Fcons k1 kon_tag [x1] (Efun (Fcons k2 kon_tag [x2] (Eapp x1 func_tag [k; x2]) Fnil) e2') Fnil)
                                                  e1', rho)). 
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 
              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                  - eassumption.
                  - intros Hc. inv H2. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv H2. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - eassumption. }
          
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }  
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
               
              2:{ intros m. eapply preord_exp_Efun_red. } simpl. 

              eapply preord_exp_refl. tci.
              eapply preord_env_P_refl. tci. }
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl. lia. } }  

        
        assert (Hex : exists x, ~ In var (k2 |: FromList (vnames)) x).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (HS2 := H6). eapply cps_cvt_rel_subset in HS2. 
        
        edestruct IH2 with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + eapply Disjoint_Included_r. eassumption. 
          eapply Union_Disjoint_l; sets.
          repeat eapply Setminus_Disjoint_preserv_r. sets. 
        + eassumption.
        + inv_setminus. intros Hc; eauto. eapply Hdis; eauto.          
        + inv_setminus.
          repeat eapply cps_env_rel_weaken; eauto; now intros Hc; eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.
        + destruct (H9 ltac:(reflexivity)). destructAll. eapply Heq in H11; [ | reflexivity ]. destructAll.
          destruct x5; try contradiction. destruct x7. eexists. split; [ | eassumption ].
          unfold fuel_sem.one in *. simpl in *. lia.
          
      - (* Match_e *)
        intros e1 e' vs dc vs' n brs r f1 f2 Heval1 IH1  Hfind Heval2 IH2.
        intros rho vnames k x vk e2 S S' f Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. 
        inv Hwf. inv Hcps. 

        assert (Hvwf : well_formed_val (Con_v dc vs')).
        { eapply eval_env_step_preserves_wf in Heval1. eassumption. reflexivity.
          eassumption. unfold well_formed_in_env.
          eapply Forall2_length in Hcenv. rewrite Hcenv. eassumption. }

        assert (Hex : exists v2, cps_val_rel (Con_v dc vs') v2).
        { eapply cps_val_rel_exists; eassumption. }
        
        assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
        { eapply ToMSet_non_member. tci. } destructAll.

        assert (Hwf := H0). inv Hwf.

        assert (HS2 := H12). eapply cps_cvt_exp_subset in HS2.

        edestruct cps_cvt_rel_branches_find_branch. eassumption. eassumption. reflexivity.
        destructAll.

        set (rho' := map_util.M.set x1 (Vconstr (dcon_to_tag default_tag dc cnstrs) vs'0)
                                    (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) k1) rho)).
              
        edestruct (set_lists_length3 rho' (rev x2) vs'0).
        { rewrite rev_length. rewrite H5, Nnat.Nat2N.id. eapply Forall2_length. eassumption. } 
        destructAll. 


        assert (Hexp : forall j, preord_exp' cenv (preord_val cenv)
                                             (cps_bound (f1 <+> fuel_sem.one (Match_e e1 n brs))) eq_fuel j
                                             (x5, x6) (Efun (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) e1', rho)).
        { intros j. eapply preord_exp_post_monotonic.
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 

              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 
              
              2:{ intros m. simpl. eapply IH1; [ | | | | | | |  eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption. 
                  - eapply Union_Disjoint_l; sets.
                  - eassumption.
                  - intros Hc. inv_setminus. eapply Hdis; eauto.
                  - eapply cps_env_rel_weaken. eassumption.
                    inv_setminus. intros Hc. eapply Hdis; eauto.
                  - rewrite M.gss. reflexivity. 
                  - eassumption. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto. rewrite M.gss. reflexivity. intros Hc; subst; eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. } 

              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Ecase_red.
                  - rewrite M.gss. reflexivity. 
                  - eassumption. }              

              eapply ctx_bind_proj_preord_exp with (vs' := []); try reflexivity. 
              - intros Hc. eapply H1 in Hc. eapply HS2 in Hc. inv_setminus. now eauto.
              - unfold rho'. rewrite M.gss. rewrite app_nil_r. reflexivity.
              - eassumption. }

          
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
            destructAll. destruct_tuples. subst. simpl in *. lia. } } 

        assert (Hex' : exists z, ~ In var (k |: FromList (x2 ++ vnames)) z).
        { eapply ToMSet_non_member. tci. } destructAll. 

        
        split. 
        
        (* Termination *)
        { intros v v' Heq Hval. subst.
          
          eapply preord_exp_post_monotonic.

          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ eassumption. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ intros i. eapply IH2 ; [ | | | | | | | eassumption | reflexivity | eassumption ]. 
                  - eapply Forall_app. split; eauto.
                    eapply Forall_rev. admit.
                  - admit. (* branches wf *)
                  - normalize_sets.
                    eapply Disjoint_Included_r. eassumption.
                    rewrite Union_commut, <- Union_assoc. 
                    eapply Union_Disjoint_l; sets.

                    eapply Disjoint_Included_r.
                    eapply Included_trans. eapply Setminus_Included. eassumption.
                    sets.
                  - eassumption. 
                  - normalize_sets.
                    intros Hc; inv Hc; eauto.
                    eapply H1 in H16. eapply HS2 in H16. inv_setminus. eapply Hdis; eauto.
                  - eapply Forall2_app.
                    rewrite <- rev_involutive with (l := x2). eapply All_Forall.Forall2_rev.
                    rewrite app_nil_end with (l := vs').
                    rewrite app_nil_end with (l := rev x2).
                    eapply cps_env_rel_extend_setlists. now constructor.
                    eapply get_list_set_lists.
                    now eapply NoDup_rev; eauto.
                    eassumption.
                    eassumption.

                    eapply cps_env_rel_weaken_setlists with (rho := rho').
                    repeat eapply cps_env_rel_weaken. eassumption.
                    intros Hc. inv_setminus. now eapply Hdis; eauto. 
                    intros Hc. inv_setminus. now eapply Hdis; eauto.
                    eassumption.
                    rewrite FromList_rev.

                    eapply Disjoint_Included_l.
                    eapply Included_trans. eassumption. eassumption. sets. 

                  - erewrite <- set_lists_not_In; [ | now eauto | ].                    
                    unfold rho'. rewrite !M.gso.
                    eassumption.
                    intros hc. inv_setminus. now eapply Hdis; eauto.
                    intros hc. inv_setminus. now eapply Hdis; eauto.
                    intros Hc.
                    eapply in_rev in Hc.
                    eapply H1 in Hc. eapply HS2 in Hc. inv_setminus. eapply Hdis; eauto. } 

          eapply preord_exp_app_compat with (P2 := eq_fuel).
          now eapply eq_fuel_compat. 
          now eapply eq_fuel_compat. 
          
          eapply preord_var_env_extend_neq. 
          eapply preord_var_env_get.
          2:{ eapply M.gss. }
          2:{ rewrite M.gss. reflexivity. }

          eapply preord_val_refl. now tci. 
          now intros Hc; subst; eauto.
          now intros Hc; subst; eauto.
          constructor.
          eapply preord_var_env_extend_eq.
          eapply preord_val_refl. now tci. now constructor. } 
        
        (* Invariant composition *)
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.            
          destructAll. destruct_tuples. subst. simpl in *. lia. } }

        
        { intros ?; subst.
          

          - destruct (H17 ltac:(reflexivity)). destructAll. eapply Hexp in H19; [ | reflexivity ]. destructAll.
            destruct x10; try contradiction. destruct x12. eexists. split; [ | eassumption ].
            
            unfold fuel_sem.one in *. simpl in *. lia. } 
        
        
      - (* Match_e OOT *)
        intros e1 vs n br f1 Hoot IH.
        intros rho vnames k x vk e' S S' f Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split.
        congruence.
        intros _. inv Hcps. inv Hwf.
        set (rho' := M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) k1) rho).
        assert (Hex : exists x, ~ In var (k1 |: FromList vnames) x).
        { eapply ToMSet_non_member. tci. } destructAll. 
        
        edestruct IH with (rho := rho'); [ | | | | | | | eassumption | ].
        + eassumption.
        + eassumption.
        + eapply Union_Disjoint_l; sets.
        + eassumption.
        + intros Hc; inv H4; eapply Hdis; eauto.
        + unfold rho'.
          eapply cps_env_rel_weaken; try eassumption.
          intros hc. inv H4. eapply Hdis; eauto.
        + unfold rho'. rewrite M.gss. reflexivity.          
        + destruct H1. reflexivity. destructAll. eexists (x2 + 1)%nat. split.
          unfold fuel_sem.one. simpl. lia.
          replace tt with (tt <+> tt) by reflexivity. eapply BStepf_run. econstructor.
          simpl. eassumption.

      - (* enil *)
        (* enil *)
        intros vs'.

        intros rho vnames e' e_app S S' vs2 xs ys ks vs'' Hwfenv Hwf
               Hdis Hdis' Hdis'' Hdis''' Hnd Hcenv Hfv Hcps Hall Hgetl.
        inv Hall. inv Hcps.
        
        edestruct (set_lists_length3 rho (ys ++ []) (vs'' ++ [])).
        { rewrite !app_nil_r. eapply get_list_length_eq. eassumption. }
        
        eexists. split. eassumption.
        intros i. 
        eapply preord_exp_post_monotonic.
        
        2:{ eapply preord_exp_refl. tci.


            assert (Henv : preord_env_P_inj cenv eq_fuel (occurs_free e') i id x rho).
            { eapply preord_env_P_inj_f_eq_subdomain.
              eapply preord_env_P_inj_set_lists_l; eauto.
              eapply preord_env_P_refl. tci.
              rewrite !app_nil_r. eapply Forall2_refl. intro. eapply preord_val_refl. tci.
              rewrite !app_nil_r. rewrite apply_r_set_list_f_eq.

              clear. induction ys. simpl.
              intros z Hin. rewrite apply_r_empty. reflexivity.
              simpl. intros z Hin.
              destruct (Coqlib.peq z a). subst. rewrite extend_gss; eauto.
              rewrite extend_gso; eauto. }

            unfold preord_env_P_inj, id in *.  eassumption. } 

        (* Invariant composition *)
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
          intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
          destructAll. destruct_tuples. subst. simpl in *. lia. }

      - (* econs *)
        intros vs' we es v vs f1 fs Heval1 IH1 Heval2 IH2.
        intros rho vnames e' e_app S S' vs2 xs ys ks vs'' Hwfenv Hwf Hdis Hdis' Hdis'' Hdis''' Hnd
               Hcenv Hfv Hcps Hall Hgetl.
        inv Hall. inv Hcps. inv Hwf.        
        
        set (rho' := M.set x1 y (M.set k1 (Vfun rho (Fcons k1 kon_tag [x1] es' Fnil) k1) rho)).
        
        replace (ys ++ x1 :: xs0) with ((ys ++ [x1]) ++ xs0) in *.
        2:{ rewrite app_cons with (a := x1) (l2 := xs0). reflexivity.  }
        
        edestruct IH2 with (ys := ys ++ [x1]) (vs'0 := vs'' ++ [y]) (rho := rho');
          [ | | | | | | | | | eassumption | eassumption | | ].
        + eassumption.
        + eassumption.
        + repeat normalize_sets.
          eapply Disjoint_Included_r.
          eapply cps_cvt_exp_subset. eassumption.
          xsets.
        + repeat normalize_sets.
          eapply Disjoint_Included; [ | | eapply Hdis' ]; sets.
        + repeat normalize_sets.
          eapply Union_Disjoint_r; sets.
          eapply Disjoint_Included; [ | | eapply Hdis'' ]; sets.
          eapply Disjoint_Included; [ | | eapply Hdis'' ]; sets.
        + repeat normalize_sets.
          inv Hnd. eapply Union_Disjoint_r; sets.
        + inv Hnd. eassumption.
        + repeat normalize_sets. unfold rho'. repeat eapply cps_env_rel_weaken.
          eassumption.
          intros Hc. eapply Hdis'; eauto.
          intros Hc. eapply Hdis'; eauto.
        + repeat normalize_sets. sets. 
        + unfold rho'. eapply get_list_app.          
          repeat normalize_sets. rewrite !get_list_set_neq. eassumption.
          intros Hc. now eapply Hdis''; eauto.
          intros Hc. now eapply Hdis'''; eauto.
          simpl. rewrite M.gss. reflexivity.
        + destructAll. 

          edestruct (set_lists_length3 rho ((ys ++ [x1]) ++ xs0) ((vs'' ++ [y]) ++ l')).
          eapply set_lists_length_eq. eassumption. 

          eexists. split.

          rewrite app_cons with (a := y). eassumption.  

          intros i. 

          eapply preord_exp_post_monotonic. 
          
          2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Efun_red. } 

              assert (Hex' : exists z, ~ In var (k1 |: FromList vnames) z).
              { eapply ToMSet_non_member. tci. } destructAll.
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply IH1; [ | | | | | | | eassumption | reflexivity | ].
                  - eassumption.
                  - eassumption.
                  - eapply Union_Disjoint_l; sets.
                    repeat normalize_sets. sets.
                  - eassumption.
                  - repeat normalize_sets.
                    intros Hc. eapply Hdis'; eauto.
                  - simpl.
                    eapply cps_env_rel_weaken. eassumption.
                    repeat normalize_sets. intros Hc. eapply Hdis'; eauto.
                  - simpl. eapply M.gss.
                  - eassumption. }
              
              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.
              
              2:{ intros m. eapply preord_exp_Eapp_red.
                  - rewrite M.gso; eauto.
                    rewrite M.gss. reflexivity.
                    intros Hc; subst. now eauto.
                  - simpl. rewrite Coqlib.peq_true. reflexivity.
                  - simpl. rewrite M.gss. reflexivity.
                  - simpl. reflexivity. }
              
              simpl in H0.

              eapply preord_exp_trans. tci. eapply eq_fuel_idemp.

              2:{ eassumption. }
 
              eapply preord_exp_refl. tci. 

              eapply uncurry_correct.preord_env_P_set_lists_extend; eauto.

              2:{ eapply Forall2_refl. intro. eapply preord_val_refl. tci. }

              unfold rho'.
 
              eapply preord_env_P_set_not_in_P_r.
              eapply preord_env_P_set_not_in_P_r.

              eapply preord_env_P_refl. now tci.

              repeat normalize_sets.
              now sets. 
              repeat normalize_sets. now sets. } 
          
          (* Invariant composition *)
          { unfold inclusion, comp, eq_fuel, one_step, cps_bound, fuel_sem.one.
            intros [[[? ?] ?] ?] [[[? ?] ?] ?] ?.
            destructAll. destruct_tuples. subst. simpl in *. lia. }

          
      - (* Var_e *)
        intros z vs v Hnth.   
        intros rho vnames k x vk e' S S' f  Henvwf Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps.
        
        eapply preord_exp_app_compat.
        
        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.
          
        + intro; intros. unfold eq_fuel, cps_bound in *. simpl in *. subst.
          unfold_all. lia.
          
        + eapply preord_var_env_extend_neq_l. 
          eapply preord_var_env_get. eapply preord_val_refl; tci.
          rewrite M.gss. reflexivity. eassumption. intros Hc; subst; eauto.
          
        + constructor; eauto.
          edestruct cps_env_rel_nth_error; eauto. destructAll.
          eapply preord_var_env_get.
          2:{ rewrite M.gss. reflexivity. }
          2:{ eassumption. }
          eapply cps_cvt_val_alpha_equiv.
          eapply eq_fuel_compat. eapply eq_fuel_compat.
          clear; now firstorder. (* TODO find inclusion refl *)
          eassumption. eassumption. 
          
      - (* Lam_e *)
        intros e vs na.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps.

        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

            2:{ intros m. eapply preord_exp_Efun_red. }

            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat. 
            now eapply eq_fuel_compat. 

            eapply preord_var_env_extend_neq.
            eapply preord_var_env_get.
            eapply preord_val_refl. now tci. now rewrite M.gss; reflexivity. eassumption.
            
            - intros Hc; subst; eauto. 
            - intros Hc; subst. inv H2. eapply Hdis; eauto.
            - constructor; eauto. 
              eapply preord_var_env_extend_eq. inv Hval.
              (* Seems similar to other cases in alpha equiv, maybe lemma? *)
              eapply preord_val_fun.
              + simpl. rewrite Coqlib.peq_true. reflexivity. 
              + simpl. rewrite Coqlib.peq_true. reflexivity. 
              + assert (Hlen : Datatypes.length names = Datatypes.length vnames).
                { simpl. eapply Forall2_length in Hcenv. 
                  eapply Forall2_length in H5.
                  replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                  congruence. }
                
                intros rho1' j vs1 vs2 Heq Hset.
                destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
                destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
                eexists. split. reflexivity. intros. 
                eapply cps_cvt_exp_alpha_equiv; try eassumption.
                * reflexivity.
                * constructor; eauto.
                * normalize_sets. intros Hc. inv Hc. inv H3; eauto. eapply H9; eauto.
                * simpl. congruence. 
                * normalize_sets. sets.
                * normalize_sets.
                  eapply Union_Disjoint_l. sets.
                  eapply Union_Disjoint_l; sets.
                * assert (Hseq : k0 |: (x0 |: FromList names) \\ [set k0] \\ [set x0] \\ FromList names <--> Empty_set _) by xsets.
                  inv H0. inv H17. clear H18. normalize_sets. simpl.
                  rewrite extend_extend_lst_commut. rewrite extend_commut.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_alt; eauto.
                  eapply preord_env_P_inj_set_not_In_P_l; eauto.
                  eapply preord_env_P_inj_set_not_In_P_r; eauto.
                  eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                  now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                  now xsets.
                  -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                     rewrite image_id in Hc.                     
                     rewrite Hseq in Hc. 
                     inv Hc; eauto. now inv H0.
                     inv H2; eapply Hdis; eauto.
                  -- intros Hc. inv Hc. inv H0. inv H11; eauto. inv H0; eauto.
                  -- intros Hc. eapply image_extend_lst_Included in Hc; eauto.
                     rewrite image_id in Hc.                     
                     rewrite Hseq in Hc. 
                     inv Hc; eauto. inv H0.
                     inv H2. eapply Hdis. constructor. now right. eassumption.
                  -- intros Hc. eapply image_extend_Included' in Hc.
                     inv Hc; eauto. eapply image_extend_lst_Included in H0; eauto.
                     rewrite Hseq, image_id in H0. inv H0; eauto. inv H3.
                     inv H4. now eapply Hdis; eauto.
                     inv H0; eauto. inv H4; eauto.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; subst; eauto. inv H4; eauto.
                  -- intros Hc; subst; eauto.
                  -- intros Hc; eauto. inv H4. eapply Hdis; eauto.
                  -- eassumption. }
        
        (* Invariant composition *) 
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound. intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct_tuples. subst. simpl. lia. } 

      - (* Fix_e *)  
        intros n vs efns.
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hstep Hcps. split; [ | congruence ].
        intros v1 v2 Heq Hval. inv Heq. inv Hcps. inv Hval.
        
        assert (Hfeq : all_fun_name fdefs = fnames).
        { eapply cps_cvt_rel_efnlst_all_fun_name; eauto. }
        
        eapply preord_exp_post_monotonic.
        2:{ eapply preord_exp_trans. tci. eapply eq_fuel_idemp. 

            2:{ intros m. eapply preord_exp_Efun_red. }
            
            simpl. eapply preord_exp_app_compat with (P2 := eq_fuel).
            now eapply eq_fuel_compat. 
            now eapply eq_fuel_compat. 

            
            eapply preord_var_env_def_funs_not_In_r.
            rewrite Same_set_all_fun_name.
            erewrite Hfeq. intros Hc. now eapply Hdis; eauto.
            
            eapply preord_var_env_extend_neq_l.
            eapply preord_var_env_get.
            eapply preord_val_refl. now tci. rewrite M.gss. reflexivity. eassumption.
            now intros Hc; subst.

            constructor; eauto.

            eapply preord_var_env_get.
            2:{ rewrite M.gss. reflexivity. } 
            2:{ rewrite def_funs_eq. reflexivity. eapply Same_set_all_fun_name.
                rewrite Hfeq. eapply nth_error_In. eassumption. } 
            
            revert f1 f0 H13 H11. generalize (N.to_nat n). induction f as [f IHf] using lt_wf_rec1. intros.

            edestruct cps_cvt_rel_efnlst_exists. eassumption. rewrite Hfeq. eassumption.
            rewrite Hfeq. eassumption. destructAll.

            edestruct L4_to_L6_util.cps_fix_rel_exists. eassumption. eassumption. eassumption. destructAll.

            eapply preord_val_fun.
            + eassumption.
            + eassumption.
            +
              assert (Hlen : Datatypes.length names = Datatypes.length vnames).
              { simpl. eapply Forall2_length in Hcenv.
                  eapply Forall2_length in H6.
                  replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                  congruence. }
              
              intros rho1' j vs1 vs2 Heq Hset.
              destruct vs1 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.  inv Hset.
              destruct vs2 as [ | ? [ | ? [ | ] ]]; simpl in *; try congruence.
              eexists. split. reflexivity. intros. repeat subst_exp.
              
              eapply cps_cvt_exp_alpha_equiv; try eassumption.
              * reflexivity.
              * constructor.
                -- intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
                   eapply in_rev in H17; eauto.
                -- eapply NoDup_app; eauto.
                   eapply NoDup_rev. eassumption.
                   rewrite FromList_rev. sets.
              * repeat normalize_sets. rewrite FromList_rev.
                intros Hc. inv Hc. inv H17; eauto. inv H17; eauto.
              * simpl. rewrite !app_length, !rev_length.
                rewrite H3. erewrite <- cps_fix_rel_length; [ | eassumption ]. congruence. 
              * repeat normalize_sets. rewrite FromList_rev.
                eapply Union_Disjoint_l. now sets.
                eapply Union_Disjoint_l.
                eapply Disjoint_Singleton_l. now eauto.
                eapply Disjoint_Included_r. eassumption. sets.
              * repeat normalize_sets. rewrite FromList_rev.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Union_Disjoint_l; sets.
                eapply Disjoint_Included_r. eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eapply Setminus_Included. eassumption.
                now sets.
                eapply Disjoint_Included; [ | | eapply Hdis ]; sets.
                eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eapply Setminus_Included.
                eapply Included_trans. eassumption. sets. 

              * inv H24. inv H29. clear H30. simpl. repeat normalize_sets. 

                assert (Hseq : (x7 |: (x8 |: (name_in_fundefs Bs :|: FromList names)) \\ [set x7] \\ [set x8] \\
                                   name_in_fundefs Bs \\ FromList names) <--> Empty_set _) by xsets. 

                rewrite extend_extend_lst_commut. rewrite extend_commut.
                eapply preord_env_P_inj_set_alt; eauto.
                eapply preord_env_P_inj_set_alt; eauto.
                
                rewrite extend_lst_app. rewrite extend_lst_rev; eauto. 

                erewrite <- cps_fix_rel_names with (fnames' := fnames0); [ | eassumption ]. 
 
 
                eapply preord_env_P_inj_def_funs_Vfun.

                -- eapply preord_env_P_inj_antimon. eapply cps_cvt_env_alpha_equiv.
                   now eapply eq_fuel_compat. now tci. now firstorder. eassumption. eassumption.
                   rewrite FromList_rev. rewrite Same_set_all_fun_name. now xsets.
                  
                -- rewrite H3. erewrite cps_fix_rel_names; [ | eassumption ].
                   eapply cps_fix_rel_length; eauto.

                -- erewrite cps_fix_rel_names with (fnames' := fnames0); [ | eassumption ]. eassumption.
                   
                -- eapply Disjoint_Included_l.
                   eapply image_extend_lst_Included. eassumption.
                   rewrite FromList_rev, image_id, <- Same_set_all_fun_name, Hseq.
                   rewrite Same_set_all_fun_name.
                   eapply Disjoint_Included_r. eassumption. sets.
                   
                -- intros. eapply IHf. lia.
                   now erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0); eauto. 
                   eassumption.

                -- replace (@Datatypes.length positive) with (@Datatypes.length var) in * by reflexivity.
                   rewrite H3. eapply cps_fix_rel_length; eauto.
                   
                -- rewrite !rev_length.
                   rewrite H3. eapply cps_fix_rel_length; eauto.

                -- intros Hc. eapply image_extend_lst_Included in Hc; eauto. rewrite image_id in Hc.
                   repeat normalize_sets. rewrite !FromList_rev in Hc. rewrite <- Same_set_all_fun_name in Hc.
                   
                   erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0),
                             <- !Same_set_all_fun_name, <- Setminus_Union in Hc; eauto.                   
                   rewrite Hseq in Hc. repeat normalize_sets. inv Hc; eauto. 
                   now eapply Same_set_all_fun_name in H17; inv H4; eauto.
                   now inv H4; eapply Hdis; eauto.
                   rewrite !app_length, !rev_length.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence. 

                -- intros Hc. eapply image_extend_Included' in Hc. inv Hc; eauto. 
                   eapply image_extend_lst_Included in H17; eauto. rewrite image_id in H17.
                   repeat normalize_sets. rewrite !FromList_rev in H17. rewrite <- Same_set_all_fun_name in H17.
                   
                   erewrite <- !cps_fix_rel_names with (Bs := Bs) (fnames' := fnames0),
                             <- !Same_set_all_fun_name, <- Setminus_Union in H17; eauto.                   
                   rewrite Hseq in H17. repeat normalize_sets. inv H17; eauto. 
                   now eapply Same_set_all_fun_name in H24; inv H12; inv H17; eauto.
                   now inv H12; inv H17; eapply Hdis; eauto.
                   rewrite !app_length, !rev_length.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence.
                   inv H17; inv H12; eauto.
                   
                -- intros Hc; subst; eauto.

                -- intros Hc; subst; inv H12; eauto. 

                -- repeat normalize_sets.
                   intros Hc. eapply in_app_or in Hc. inv Hc; eauto.
                   eapply in_rev in H17; eauto.

                -- repeat normalize_sets. inv H12. inv H17.                    
                   intros Hc. eapply in_app_or in Hc. inv Hc.
                   eapply in_rev in H17; eauto. eapply Hdis; eauto.

                -- rewrite !app_length, !rev_length.
                   erewrite H3, <- cps_fix_rel_length; [ | eassumption ]. congruence. } 

        
        (* Invariant composition *) 
        { unfold inclusion, comp, eq_fuel, one_step, cps_bound. intros [[[? ?] ?] ?] [[[? ?] ?] ?] H.
          destructAll. destruct_tuples. subst. simpl. lia. } 

      - (* OOT *)
        intros vs e c Hlt. 
        intros rho vnames k x vk e' S S' f Hwfenv Hwf Hdis Hnin1 Hnin2 Hcenv Hcps. split.
        congruence.
        intros _.
        unfold fuel_sem.one, lt in *. simpl in *. 
        eexists 0%nat. split. lia.
        constructor 1. unfold algebra.one. simpl. lia.

      - (* STEP *)
        now eauto. (* Immediate from IH for eval_step *)
        
    Abort. 
    
End Post.
