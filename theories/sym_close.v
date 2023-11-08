From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From miniactris Require Export sub.

Definition new : val := new1.
Definition recv : val := recv1.
Definition send : val := λ: "l" "v",
  let: "l'" := new1 #() in
  send1 "l" ("v","l'");; "l'".
Definition sym_close : val := λ: "l",                                            (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=ae2ce9d8 *)
  if: CAS "l" NONE (SOME #()) then #() else Free "l".

Section sym_close_proofs.
  Context `{!heapGS Σ, !chanG Σ}.
  Let N := nroot .@ "chan".
  Notation prot := (prot Σ).

  Definition prot' : ofe := optionO prot.                                        (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=6466b725 *)

  Definition end_inv (γ1 γ2 : gname) (l : loc) : iProp Σ :=                      (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=3c5fffb4 *)
    l ↦ NONEV ∨
    (l ↦ SOMEV #() ∗ (tok γ1 ∨ tok γ2)) ∨
    (tok γ1 ∗ tok γ2).

  Lemma end_inv_iff γ1 γ2 l : end_inv γ1 γ2 l ⊣⊢ end_inv γ2 γ1 l.
  Proof.
    by rewrite /end_inv (bi.or_comm (tok γ1) (tok γ2))
       (bi.sep_comm (tok γ1) (tok γ2)).
  Qed.

  Definition is_end (ch : val) : iProp Σ :=
    ∃ γ1 γ2 (l : loc), ▷ ⌜ch = #l⌝ ∗ inv N (end_inv γ1 γ2 l) ∗ ▷ tok γ1.

  Definition is_chan' (ch : val) (p : prot') :=                                  (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=afded129 *)
    from_option (is_chan ch) (is_end ch) p.

  Definition dual' : prot' → prot' := fmap dual.                                 (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=0ab8814a *)

  Definition end_prot : prot' := None.

  Lemma sym_close_spec ch :                                                      (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=8769f222 *)
    {{{ is_chan' ch end_prot }}} sym_close ch {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "(%γ1 & %γ2 & %l & >-> & #Hinv & >Htok) HΨ". wp_lam. wp_pures.
    wp_bind (CmpXchg _ _ _). iInv N as "[H|[[H1 H2]|>[H1 H2]]]".
    - wp_cmpxchg_suc. iModIntro. iSplitL "H Htok".
      + iModIntro. unfold end_inv. eauto with iFrame.
      + wp_pures. iModIntro. by iApply "HΨ".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Htok H2".
      + iModIntro. unfold end_inv.
        iDestruct "H2" as "[H2|H2]"; last eauto with iFrame.
        iDestruct (own_valid_2 with "Htok H2") as %[].
      + wp_pures. wp_free. iModIntro. by iApply "HΨ".
    - iDestruct (own_valid_2 with "Htok H1") as %[].
  Qed.

  (* ?x <v> {P}. p *)
  Definition recv_prot' {A} (v : A → val) (Φ : A -d> iPropO Σ) (p : A -d> prot') : prot' :=
    Some (false, λ r, ∃ x ch', ⌜r = PairV (v x) ch'⌝ ∗ Φ x ∗ is_chan' ch' (p x))%I.

  (* !x <v> {P}. p x *)
  Definition send_prot' {A} (v : A → val) (Φ : A -d> iPropO Σ) (p : A -d> prot') : prot' :=
    dual' (recv_prot' v Φ (dual'∘p)).

  Lemma new_spec_end' :
    {{{ True }}}
      new #()
    {{{ ch, RET ch; is_chan' ch end_prot ∗ is_chan' ch end_prot }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ1) "Hγ1"; first done.
    iMod (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
    iMod (inv_alloc N _ (end_inv γ1 γ2 l) with "[Hl]") as "#?"; [by iLeft|].
    iApply "HΦ".
    iSplitL "Hγ1".
    - iExists _, _, _. eauto with iFrame.
    - iExists _, _, _. rewrite end_inv_iff. eauto with iFrame.
  Qed.

  Lemma new_spec' p :
    {{{ True }}}
      new #()
    {{{ ch, RET ch; is_chan' ch p ∗ is_chan' ch (dual' p) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    destruct p.
    - iApply new1_spec; [done|].
      iIntros "!>" (ch) "[Hch1 Hch2]". iApply "HΦ". by iFrame.
    - iApply new_spec_end'; [done|].
      iIntros "!>" (ch) "[Hch1 Hch2]". iApply "HΦ". by iFrame.
  Qed.

  Lemma recv_spec' {A} ch (v : A → val) Φ p :
    {{{ is_chan' ch (recv_prot' v Φ p) }}}
      recv ch
    {{{ x ch', RET (v x, ch'); is_chan' ch' (p x) ∗ Φ x }}}.
  Proof.
    iIntros (Ψ) "Hr HΨ". wp_apply (recv1_spec with "Hr").
    iIntros (ch') "(%x&%w&->&?&?)". iApply "HΨ". iFrame.
  Qed.

  Lemma send_spec' {A} ch (v : A → val) Φ p x :
    {{{ is_chan' ch (send_prot' v Φ p) ∗ ▷ Φ x }}}
      send ch (v x)
    {{{ ch', RET ch'; is_chan' ch' (p x) }}}.
  Proof.
    iIntros (Ψ) "[Hs HΦ] HΨ". wp_lam. wp_let.
    wp_smart_apply (new_spec' (p x) with "[//]").
    iIntros (ch') "[H1 H2]". wp_let.
    wp_smart_apply (send1_spec with "[$Hs HΦ H2]").
    - simpl. iExists _,_. iSplit; first done. iFrame.
    - iIntros "_". wp_seq. by iApply "HΨ".
  Qed.

  Definition subprot' (p1' p2' : prot') : iProp Σ :=                             (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=dfae3618 *)
    match p1',p2' with
    | Some p1, Some p2 => subprot p1 p2
    | None, None => True
    | _, _ => False
    end.

  Global Instance is_end_is_except_0 ch : IsExcept0 (is_end ch).
  Proof.
    rewrite /IsExcept0 /is_end. repeat (setoid_rewrite bi.except_0_exist).
    do 6 f_equiv. rewrite !bi.except_0_sep !bi.except_0_later.
    by rewrite except_0_inv.
  Qed.
  Global Instance is_chan'_is_except_0 ch p : IsExcept0 (is_chan' ch p).
  Proof. destruct p; apply _. Qed.

  Lemma subprot_is_chan' ch p p' :
    ▷ subprot' p p' -∗ is_chan' ch p -∗ is_chan' ch p'.
  Proof.
    iIntros "Hsp Hch".
    destruct p, p'; simpl; try by iMod "Hsp".
    by iApply (subprot_is_chan with "[$]").
  Qed.

  Lemma subprot_dual' p1 p2 : subprot' (dual' p1) (dual' p2) ⊣⊢ subprot' p2 p1.
  Proof. destruct p1,p2; rewrite //= subprot_dual //. Qed.

  Lemma subprot_end' : ⊢ subprot' None None.
  Proof. done. Qed.

  Lemma subprot_recv' {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x1, Φ1 x1 -∗ ∃ x2, ⌜v1 x1 = v2 x2⌝ ∗ Φ2 x2 ∗ ▷ subprot' (p1 x1) (p2 x2)) -∗
    subprot' (recv_prot' v1 Φ1 p1) (recv_prot' v2 Φ2 p2).
  Proof.
    rewrite {2}/subprot' /subprot. iIntros "H %v /=".
    iIntros "(%x1 & %ch & -> & HΦ1 & Hch)".
    iDestruct ("H" with "HΦ1") as (x2 Heq) "[H1 H2]".
    iExists _,_. iSplit; first rewrite Heq //. iFrame.
    by iApply (subprot_is_chan' with "[$]").
  Qed.

  Lemma subprot_send' {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x2, Φ2 x2 -∗ ∃ x1, ⌜v2 x2 = v1 x1⌝ ∗ Φ1 x1 ∗ ▷ subprot' (p1 x1) (p2 x2)) -∗
    subprot' (send_prot' v1 Φ1 p1) (send_prot' v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite subprot_dual'.
    iApply subprot_recv'. simpl.
    by setoid_rewrite subprot_dual'.
  Qed.

End sym_close_proofs.
