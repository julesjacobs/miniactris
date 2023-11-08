From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang.lib Require Import assert.

Definition new1 : val := λ: <>, ref NONE.                                        (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=6d4a36a8 *)
Definition recv1 : val :=                                                        (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=fbf7b3d2 *)
  rec: "recv1" "l" :=
    match: !"l" with
      NONE => "recv1" "l"
    | SOME "v" => Free "l";; "v"
    end.
Definition send1 : val := λ: "l" "v",                                            (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=f5ebc56f *)
    "l" <- SOME ("v").

Class chanG Σ := LockG { chan_tokG : inG Σ (exclR unitO) }.
Local Existing Instance chan_tokG.
Definition chanΣ : gFunctors := #[GFunctor (exclR unitO)].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Definition prot Σ : ofe := prodO boolO (val -d> iPropO Σ).                       (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=6b4721a9 *)

Section proof_base.
  Context `{!heapGS Σ, !chanG Σ}.
  Let N := nroot .@ "chan".
  Notation prot := (prot Σ).

  Definition tok (γ : gname) : iProp Σ := own γ (Excl ()).

  Definition chan_inv (γ1 γ2 : gname) (l : loc)                                  (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=de8d955e *)
                      (Φ : val → iProp Σ) : iProp Σ :=
    (l ↦ NONEV) ∨
    (∃ v, l ↦ SOMEV v ∗ tok γ1 ∗ Φ v) ∨
    (tok γ1 ∗ tok γ2).

  Definition is_chan0 (ch : val) (p : prot) : iProp Σ :=                         (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=2239f976 *)
    ∃ γ1 γ2 (l : loc),
      ▷ ⌜ch = #l⌝ ∗ inv N (chan_inv γ1 γ2 l p.2) ∗ ▷ tok (if p.1 then γ1 else γ2).

  Definition dual (p : prot) : prot := (negb p.1, p.2).                          (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=5cc878c4 *)

  Lemma pointsto_to_chan l p :
    l ↦ NONEV -∗ |={⊤}=> is_chan0 #l p ∗ is_chan0 #l (dual p).
  Proof.
    iIntros "Hl".
    iMod (own_alloc (Excl ())) as (γ1) "Hγ1"; first done.
    iMod (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
    iMod (inv_alloc N _ (chan_inv γ1 γ2 l p.2) with "[Hl]") as "#?"; [by iLeft|].
    destruct p as [[]?]; [iSplitL "Hγ1"|iSplitL "Hγ2"];
      iExists _, _; by eauto with iFrame.
  Qed.

  Lemma new1_spec0 p :                                                           (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=f1f7640b *)
    {{{ True }}} new1 #() {{{ ch, RET ch; is_chan0 ch p ∗ is_chan0 ch (dual p) }}}.
  Proof.
    iIntros (Ψ) "_ HΨ". wp_lam. wp_alloc l as "Hl".
    iMod (pointsto_to_chan with "Hl") as "[H1 H2]".
    iApply "HΨ". by eauto with iFrame.
  Qed.

  Lemma send1_spec0 ch P v :                                                     (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=397c74c2 *)
    {{{ is_chan0 ch (true,P) ∗ ▷ P v }}} send1 ch v {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "[(%γ1 & %γ2 & %l & >-> & #Hinv & >Htok) HP] Hφ /=".
    wp_lam; wp_pures.
    iInv N as "[Hl|[(%w & Hl & >Htok' & HΦ')|>[Htok' Htok'']]]";
      [|iDestruct (own_valid_2 with "Htok Htok'") as %[]..].
    wp_store. iSplitR "Hφ"; last by iApply "Hφ".
    rewrite /chan_inv; eauto 10 with iFrame.
  Qed.

  Lemma recv1_spec0 ch P :                                                       (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=1a598d64 *)
    {{{ is_chan0 ch (false,P) }}} recv1 ch {{{ v, RET v; P v }}}.
  Proof.
    iIntros (φ) "(%γ1 & %γ2 & %l & >-> & #Hinv & >Htok) Hφ /=".
    iLöb as "IH". wp_rec. wp_bind (Load _).
    iInv N as "[Hl|[(%w & Hl & Htok' & HΦ')|>[Htok' Htok'']]]".
    - wp_load. iModIntro. iSplitL "Hl"; [iNext; by iLeft|].
      wp_match. iApply ("IH" with "Htok Hφ").
    - wp_load. iModIntro. iSplitL "Htok Htok'".
      + rewrite /chan_inv. by eauto with iFrame.
      + wp_match. wp_free. wp_seq. iModIntro. by iApply "Hφ".
    - iDestruct (own_valid_2 with "Htok Htok''") as %[].
  Qed.

  Lemma dual_dual p : dual (dual p) = p.                                         (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=c5318bd3 *)
  Proof. by destruct p as [[] ?]. Qed.
  Global Instance dual_ne : NonExpansive dual.
  Proof. solve_proper. Qed.
  Global Instance dual_proper : Proper ((≡) ==> (≡)) dual.
  Proof. solve_proper. Qed.

  Global Instance chan_inv_ne γ1 γ2 l n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (chan_inv γ1 γ2 l).
  Proof. solve_proper. Qed.
  Global Instance chan_inv_proper γ1 γ2 l :
    Proper (pointwise_relation _ (≡) ==> (≡)) (chan_inv γ1 γ2 l).
  Proof. solve_proper. Qed.

  Global Instance is_chan0_is_except_0 ch p : IsExcept0 (is_chan0 ch p).
  Proof.
    rewrite /IsExcept0 /is_chan0. repeat (setoid_rewrite bi.except_0_exist).
    do 6 f_equiv. rewrite !bi.except_0_sep !bi.except_0_later.
    by rewrite except_0_inv.
  Qed.
  Global Instance is_chan0_contractive ch : Contractive (is_chan0 ch).           (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=0ab400f2 *)
  Proof.
    intros n [??] [??] Hpair; solve_proper_prepare.
    repeat first [f_contractive; destruct Hpair; simplify_eq/=| f_equiv].
  Qed.
  Global Instance is_chan0_ne ch : NonExpansive (is_chan0 ch).
  Proof. solve_proper. Qed.
  Global Instance is_chan0_proper ch : Proper ((≡) ==> (≡)) (is_chan0 ch).
  Proof. solve_proper. Qed.
End proof_base.

Global Typeclasses Opaque is_chan0.

Section base_examples.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition prog_single : val :=                                                (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=bcd4fd26 *)
    λ: "<>",
      let: "c" := new1 #() in
      Fork (let: "l" := ref #42 in send1 "c" "l");;
      let: "l" := recv1 "c" in assert: (!"l" = #42).

  Definition prot_single : prot :=                                               (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=8744da2d *)
    (false, λ (v:val), ∃ (l:loc), ⌜v = #l⌝ ∗ l ↦ #42)%I.

  Lemma prog_add_spec : {{{ True }}} prog_single #() {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new1_spec0 prot_single); [done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_alloc l as "Hl".
      wp_smart_apply (send1_spec0 with "[$Hch2 Hl]"); [|done].
      iIntros "!>". iExists _. by iFrame.
    - wp_smart_apply (recv1_spec0 with "Hch1").
      iIntros (v) "Hl". iDestruct "Hl" as (l ->) "Hl".
      wp_smart_apply wp_assert. wp_load. wp_pures.
      iModIntro. iSplit; [done|]. by iApply "HΦ".
  Qed.

End base_examples.
