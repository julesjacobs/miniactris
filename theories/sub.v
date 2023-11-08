From miniactris Require Export base.

Section proof_sub.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition subprot (p1 p2 : prot) : iProp Σ :=                                 (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=9b360e4f *)
    match p1.1, p2.1 with
    | true, true => ∀ v, p2.2 v -∗ p1.2 v
    | false, false => ∀ v, p1.2 v -∗ p2.2 v
    | _, _ => False
    end.

  Lemma subprot_refl p : ⊢ subprot p p.
  Proof. destruct p as [[] P]; rewrite /subprot /=; eauto. Qed.

  Lemma subprot_dual p1 p2 : subprot (dual p1) (dual p2) ⊣⊢ subprot p2 p1.
  Proof. destruct p1 as [[]]; destruct p2 as [[]]; eauto. Qed.

  Lemma subprot_trans p1 p2 p3 : subprot p1 p2 -∗ subprot p2 p3 -∗ subprot p1 p3.
  Proof.
    iIntros "Hsp1 Hsp2".
    destruct p1 as [[] P1], p2 as [[] P2], p3 as [[] P3];
      rewrite /subprot //=; iIntros (v) "H //";
      by do 2 (iApply "Hsp1" || iApply "Hsp2").
  Qed.

  Lemma subprot_send1 Φ Ψ : (∀ v, Ψ v -∗ Φ v) -∗ subprot (true,Φ) (true,Ψ).
  Proof. by eauto. Qed.

  Lemma subprot_recv1 Φ Ψ : (∀ v, Φ v -∗ Ψ v) -∗ subprot (false,Φ) (false,Ψ).
  Proof. rewrite -subprot_dual. by apply subprot_send1. Qed.

  Definition is_chan (ch : val) (p : prot) : iProp Σ :=                          (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=4e9f1a19 *)
    ∃ p', ▷ subprot p' p ∗ is_chan0 ch p'.

  Lemma is_chan0_is_chan ch p : is_chan0 ch p -∗ is_chan ch p.                   (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=5dc73eb1 *)
  Proof. iIntros "H". iExists p. iFrame. iApply subprot_refl. Qed.

  Lemma subprot_is_chan ch p p' :                                                (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=858623e8 *)
    ▷ subprot p p' -∗ is_chan ch p -∗ is_chan ch p'.
  Proof.
    iIntros "Hsp [%p'' [Hsp' Hch]]".
    iExists _. iFrame. by iApply (subprot_trans with "Hsp'").
  Qed.

  Lemma new1_spec p :                                                            (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=2bb616f2 *)
    {{{ True }}} new1 #() {{{ ch, RET ch; is_chan ch p ∗ is_chan ch (dual p) }}}.
  Proof.
    iIntros (Ψ) "_ HΨ". wp_apply new1_spec0; first done.
    iIntros (ch) "[H1 H2]". iApply "HΨ".
    iSplitL "H1"; by iApply is_chan0_is_chan.
  Qed.

  Lemma send1_spec ch P v :                                                      (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=a2c83119 *)
    {{{ is_chan ch (true,P) ∗ ▷ P v }}} send1 ch v {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "[[%p' [Hsp Hch]] Hp] Hφ".
    destruct p' as [[] P']; rewrite /subprot /=; last by iMod "Hsp".
    wp_apply (send1_spec0 with "[$Hch Hp Hsp]"); [by iApply "Hsp"|done].
  Qed.

  Lemma recv1_spec ch P :                                                        (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=b3b2590a *)
    {{{ is_chan ch (false,P) }}} recv1 ch {{{ v, RET v; P v }}}.
  Proof.
    iIntros (φ) "[%p' [Hsp Hch]] Hφ".
    destruct p' as [[] P']; rewrite /subprot /=; first by iMod "Hsp".
    wp_apply (recv1_spec0 with "[$]"). iIntros (v) "Hv". iApply "Hφ". by iApply "Hsp".
  Qed.

  Global Instance subprot_ne : NonExpansive2 subprot.
  Proof. intros ? [??] [??] [??] [??] [??] [??]. simplify_eq/=. solve_proper. Qed.
  Global Instance subprot_proper : Proper ((≡) ==> (≡) ==> (≡)) subprot.
  Proof. apply ne_proper_2, _. Qed.

  Global Instance is_chan_is_except_0 ch p : IsExcept0 (is_chan ch p).
  Proof.
    rewrite /IsExcept0 /is_chan bi.except_0_exist. f_equiv=> p'.
    by rewrite bi.except_0_sep bi.except_0_later (is_except_0 (is_chan0 _ _)).
  Qed.
  Global Instance is_chan_contractive ch : Contractive (is_chan ch).
  Proof. solve_contractive. Qed.
  Global Instance is_chan_ne ch : NonExpansive (is_chan ch).
  Proof. solve_proper. Qed.
  Global Instance is_chan_proper ch : Proper ((≡) ==> (≡)) (is_chan ch).
  Proof. solve_proper. Qed.
End proof_sub.

Global Typeclasses Opaque subprot is_chan.
