From miniactris Require Export sub.
From iris.heap_lang.lib Require Import assert.

Definition new : val := new1.
Definition recv : val := recv1.
Definition send : val := λ: "l" "v",
  let: "l'" := new1 #() in
  send1 "l" ("v","l'");; "l'".
Definition send_close : val := λ: "l" "v", send1 "l" ("v", #()).                 (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=69457c84 *)

Section send_close_proofs.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition prot' : ofe := optionO prot.                                        (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=ab10e61c *)

  Definition is_chan' (ch : val) (p : prot') : iProp Σ :=                        (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=c32ff222 *)
    from_option (is_chan ch) (▷ ⌜ch = #()⌝)%I p.

  Definition dual' : prot' → prot' := fmap dual.

  Definition end_prot : prot' := None.

  (* ?x <v x> {P x}. p x *)
  Definition recv_prot' {A} (v : A → val) (Φ : A → iPropO Σ) (p : A → prot') : prot' :=
    Some (false, λ r, ∃ x ch', ⌜r = (v x, ch')%V⌝ ∗ Φ x ∗ is_chan' ch' (p x))%I.

  (* !x <v x> {P x}. p x *)
  Definition send_prot' {A} (v : A → val) (Φ : A → iPropO Σ) (p : A → prot') : prot' :=
    dual' (recv_prot' v Φ (dual' ∘ p)).

  Definition subprot' (p1' p2' : prot') : iProp Σ :=
    match p1',p2' with
    | Some p1, Some p2 => subprot p1 p2
    | None, None => True
    | _, _ => False
    end.

  Global Instance dual_ne : NonExpansive dual'.
  Proof. solve_proper. Qed.
  Global Instance dual_proper : Proper ((≡) ==> (≡)) dual'.
  Proof. solve_proper. Qed.

  Global Instance subprot_ne' : NonExpansive2 subprot'.
  Proof. solve_proper. Qed.
  Global Instance subprot_proper' : Proper ((≡) ==> (≡) ==> (≡)) subprot'.
  Proof. apply ne_proper_2, _. Qed.

  Global Instance is_chan_is_except_0' ch p : IsExcept0 (is_chan' ch p).
  Proof. destruct p; apply _. Qed.

  Global Instance is_chan_contractive' ch : Contractive (is_chan' ch).
  Proof.
    apply (uPred.contractive_internal_eq (M:=iResUR Σ)). iIntros (p p') "#H".
    rewrite option_equivI. destruct p as [p|], p' as [p'|]; simpl; last done.
    - by iApply f_equivI_contractive.
    - iApply prop_ext. iIntros "!>". iSplit; [by auto|]. by iMod "H".
    - iApply prop_ext. iIntros "!>". iSplit; [|by auto]. by iMod "H".
  Qed.
  Global Instance is_chan_ne' ch : NonExpansive (is_chan' ch).
  Proof. solve_proper. Qed.
  Global Instance is_chan_proper' ch : Proper ((≡) ==> (≡)) (is_chan' ch).
  Proof. solve_proper. Qed.

  Global Instance recv_prot_contractive' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) recv_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /recv_prot'.
    apply: Some_ne. apply: pair_ne; [done|]. intros v.
    do 6 f_equiv; [by repeat f_equiv..|].
    f_contractive. by rewrite Hpeq.
  Qed.
  Global Instance recv_prot_ne' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) recv_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /recv_prot'.
    apply: Some_ne. apply: pair_ne; [done|]. intros v. solve_proper.
  Qed.
  Global Instance recv_prot_proper' A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) recv_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /recv_prot'.
    apply: Some_proper. apply: pair_proper; [done|]. intros v. solve_proper.
  Qed.

  Global Instance send_prot_contractive' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) send_prot'.
  Proof. intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /send_prot'.
         apply dual_ne. apply recv_prot_contractive'; [done..|].
         f_equiv. destruct n; [by apply dist_later_0|]=> /=.
         specialize (Hpeq a). apply dist_later_S in Hpeq.
         apply dist_later_S. by repeat f_equiv.
  Qed.
  Global Instance send_prot_ne' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) send_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /send_prot'.
    apply: Some_proper. apply: pair_proper; [done|]. intros v. solve_proper.
  Qed.
  Global Instance send_prot_proper' A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) send_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /send_prot'.
    apply: Some_proper. apply: pair_proper; [done|]. intros v. solve_proper.
  Qed.

  Lemma new_spec' p :                                                            (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=bd9e2d7d *)
    is_Some p →
    {{{ True }}}
      new #()
    {{{ ch, RET ch; is_chan' ch p ∗ is_chan' ch (dual' p) }}}.
  Proof.
    iIntros ([?->] Φ) "_ HΦ". iApply new1_spec; [done|].
    iIntros "!>" (ch) "[Hch1 Hch2]". iApply "HΦ". by iFrame.
  Qed.

  Lemma recv_spec' {A} ch (v : A → val) Φ p :                                    (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=b8e66d9f *)
    {{{ is_chan' ch (recv_prot' v Φ p) }}}
      recv ch
    {{{ x ch', RET (v x, ch'); is_chan' ch' (p x) ∗ Φ x }}}.
  Proof.
    iIntros (Ψ) "Hr HΨ". wp_apply (recv1_spec with "Hr").
    iIntros (ch') "(%x&%w&->&?&?)". iApply "HΨ". iFrame.
  Qed.

  Lemma send_spec' {A} x ch (v : A → val) Φ p :                                  (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=02adf44c *)
    p x ≢ end_prot →
    {{{ is_chan' ch (send_prot' v Φ p) ∗ ▷ Φ x }}}
      send ch (v x)
    {{{ ch', RET ch'; is_chan' ch' (p x) }}}.
  Proof.
    iIntros (Hp Ψ) "[Hs HΦ] HΨ". wp_lam. wp_let.
    destruct (p x) as [p0|] eqn:Hp0; last done.
    wp_smart_apply (new1_spec p0 with "[//]").
    iIntros (ch') "[H1 H2]". wp_let. wp_smart_apply (send1_spec with "[$Hs HΦ H2]").
    - simpl. iExists _,_. iSplit; first done. rewrite Hp0. iFrame.
    - iIntros "_". wp_seq. by iApply "HΨ".
  Qed.

  Lemma send_close_spec' {A} x ch (v : A → val) Φ p :                            (* https://apndx.org/pub/mpy9/miniactris.pdf#nameddest=8d042d3f *)
    p x ≡ end_prot →
    {{{ is_chan' ch (send_prot' v Φ p) ∗ ▷ Φ x }}}
      send_close ch (v x)
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Hp0 Ψ) "[Hs HΦ] HΨ". wp_lam. wp_let.
    wp_smart_apply (send1_spec with "[$Hs HΦ]").
    - simpl. iExists _,_. iSplit; first done. rewrite Hp0. by iFrame.
    - iIntros "_". by iApply "HΨ".
  Qed.

  Lemma subprot_is_chan' ch p p' :
    ▷ subprot' p p' -∗ is_chan' ch p -∗ is_chan' ch p'.
  Proof.
    iIntros "Hsp ?". destruct p, p'; simpl; try by iMod "Hsp".
    by iApply (subprot_is_chan with "[$]").
  Qed.

  Lemma subprot_dual' p1 p2 : subprot' (dual' p1) (dual' p2) ⊣⊢ subprot' p2 p1.
  Proof.
    destruct p1,p2; rewrite //= subprot_dual //.
  Qed.

  Lemma subprot_refl' p : ⊢ subprot' p p.
  Proof. destruct p; [apply subprot_refl|done]. Qed.

  Lemma subprot_end' : ⊢ subprot' None None.
  Proof. apply subprot_refl'. Qed.

  Lemma subprot_recv' {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x1, Φ1 x1 -∗ ∃ x2, ⌜v1 x1 = v2 x2⌝ ∗ Φ2 x2 ∗ ▷ subprot' (p1 x1) (p2 x2)) -∗
    subprot' (recv_prot' v1 Φ1 p1) (recv_prot' v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite {2}/subprot' /subprot /=. iIntros "%v".
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

  Lemma dual_dual' p : dual' (dual' p) = p.
  Proof. destruct p as [p|]; [|done]. by destruct p as [[] ?]. Qed.
  Lemma recv_prot_dual' {A} (v : A → val) Φ p :
    dual' (recv_prot' v Φ p) ≡ send_prot' v Φ (dual'∘p).
  Proof.
    rewrite /send_prot'. f_equiv. eapply recv_prot_proper'; intro; try done.
    by rewrite /= dual_dual'.
  Qed.
  Lemma send_prot_dual' {A} (v : A → val) Φ p :
    dual' (send_prot' v Φ p) ≡ recv_prot' v Φ (dual'∘p).
  Proof. simpl. done. Qed.

End send_close_proofs.
