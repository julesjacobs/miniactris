From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang.lib Require Import assert.

Definition new1 : val := λ: <>, ref NONE.
Definition recv1 : val :=
  rec: "recv1" "l" :=
    let: "v" := Xchg "l" NONEV in
    match: "v" with
      NONE => "recv1" "l"
    | SOME "x" => "x"
    end.
Definition send1 : val := λ: "l" "v",
    "l" <- SOME ("v").

Definition prot Σ : ofe := (val -d> iPropO Σ).

Section proof_base.
  Context `{!heapGS Σ}.
  Let N := nroot .@ "chan".
  Notation prot := (prot Σ).

  Definition chan_inv (l : loc) (Φ : val → iProp Σ) : iProp Σ :=
    (l ↦ NONEV) ∨ (∃ v, l ↦ SOMEV v ∗ Φ v).

  Definition is_chan0 (ch : val) (p : prot) : iProp Σ :=
    ∃ (l : loc), ▷ ⌜ch = #l⌝ ∗ inv N (chan_inv l p).

  Lemma pointsto_to_chan l p :
    l ↦ NONEV -∗ |={⊤}=> is_chan0 #l p.
  Proof.
    iIntros "Hl".
    iMod (inv_alloc N _ (chan_inv l p) with "[Hl]") as "#?"; [by iLeft|].
    iModIntro. iExists _. iSplitL; [done|]. done.
  Qed.

  Lemma new1_spec0 p :
    {{{ True }}} new1 #() {{{ ch, RET ch; is_chan0 ch p ∗ is_chan0 ch p }}}.
  Proof.
    iIntros (Ψ) "_ HΨ". wp_lam. wp_alloc l as "Hl".
    iMod (pointsto_to_chan with "Hl") as "H1".
    iApply "HΨ". by eauto with iFrame.
  Qed.

  Lemma send1_spec0 ch P v :
    {{{ is_chan0 ch P ∗ ▷ P v }}} send1 ch v {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "[(%l & >-> & #Hinv) HP] Hφ /=".
    wp_lam; wp_pures.
    iInv N as "[Hl|(%w & Hl & HΦ')]".
    - wp_store. iSplitR "Hφ"; last by iApply "Hφ".
      rewrite /chan_inv; eauto 10 with iFrame.
    - wp_store. iSplitR "Hφ"; last by iApply "Hφ".
      rewrite /chan_inv; eauto 10 with iFrame.
      iModIntro. iRight. iNext. iExists v. iFrame.
  Qed.

  Lemma recv1_spec0 ch P :
    {{{ is_chan0 ch P }}} recv1 ch {{{ v, RET v; P v }}}.
  Proof.
    iIntros (φ) "(%l & >-> & #Hinv) Hφ /=".
    iLöb as "IH". wp_rec. wp_bind (Xchg _ _).
    iInv N as "[Hl|(%w & Hl & HΦ')]".
    - wp_xchg. iModIntro.
      iSplitL "Hl"; [iNext; by iLeft|].
      wp_pures. by iApply "IH".
    - wp_xchg. iModIntro. iSplitL "Hl".
      + rewrite /chan_inv. by eauto with iFrame.
      + wp_pures. iModIntro. by iApply "Hφ".
  Qed.

  Global Instance chan_inv_ne l n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (chan_inv l).
  Proof. solve_proper. Qed.
  Global Instance chan_inv_proper l :
    Proper (pointwise_relation _ (≡) ==> (≡)) (chan_inv l).
  Proof. solve_proper. Qed.

  Global Instance is_chan0_is_except_0 ch p : IsExcept0 (is_chan0 ch p).
  Proof.
    rewrite /IsExcept0 /is_chan0. repeat (setoid_rewrite bi.except_0_exist).
    do 2 f_equiv. rewrite !bi.except_0_sep !bi.except_0_later.
    by rewrite except_0_inv.
  Qed.
  Global Instance is_chan0_contractive ch : Contractive (is_chan0 ch).
  Proof.
    intros n Hpair; solve_proper_prepare.
    by repeat first [f_contractive; destruct Hpair; simplify_eq/=| f_equiv].
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

  Definition prog_single : val :=
    λ: "<>",
      let: "c" := new1 #() in
      Fork (let: "l" := ref #42 in send1 "c" "l");;
      let: "l" := recv1 "c" in assert: (!"l" = #42).

  Definition prot_single : prot :=
    (λ (v:val), ∃ (l:loc), ⌜v = #l⌝ ∗ l ↦ #42)%I.

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

Definition new : val := new1.
Definition recv : val := recv1.
Definition send : val := λ: "l" "v",
  let: "l'" := new1 #() in
  send1 "l" ("v","l'");; "l'".
Definition wait : val := recv1.
Definition close : val := λ: "l", send1 "l" #().

Section session_proofs.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).
  Notation is_chan := (is_chan0).

  (** !? x <v> {P}. p *)
  Definition ses_prot {A} (v : A → val) (Φ : A → iPropO Σ) (p : A → prot) : prot :=
    (λ r, ∃ x ch', ⌜r = (v x, ch')%V⌝ ∗ Φ x ∗ is_chan ch' (p x))%I.

  (** End!? *)
  Definition end_prot : prot := (λ r, ⌜r = #()⌝)%I.

  Lemma new_spec p :
    {{{ True }}} new #() {{{ ch, RET ch; is_chan ch p ∗ is_chan ch p }}}.
  Proof. apply new1_spec0. Qed.

  Lemma recv_spec {A} ch (v : A → val) Φ p :
    {{{ is_chan ch (ses_prot v Φ p) }}}
      recv ch
    {{{ x ch', RET (v x, ch'); is_chan ch' (p x) ∗ Φ x }}}.
  Proof.
    iIntros (Ψ) "Hr HΨ". wp_apply (recv1_spec0 with "Hr").
    iIntros (ch') "(%x&%w&->&?&?)". iApply "HΨ". iFrame.
  Qed.

  Lemma send_spec {A} x ch (v : A → val) Φ p :
    {{{ is_chan ch (ses_prot v Φ p) ∗ ▷ Φ x }}}
      send ch (v x)
    {{{ ch', RET ch'; is_chan ch' (p x) }}}.
  Proof.
    iIntros (Ψ) "[Hs HΦ] HΨ". wp_lam. wp_smart_apply (new_spec (p x) with "[//]").
    iIntros (ch') "[H1 H2]". wp_smart_apply (send1_spec0 with "[$Hs HΦ H2]").
    - simpl. iNext. iExists _, _. iFrame. done.
    - iIntros "_". wp_seq. by iApply "HΨ".
  Qed.

  Lemma wait_spec ch :
    {{{ is_chan ch end_prot }}} wait ch {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hch HΨ". wp_apply (recv1_spec0 with "Hch").
    iIntros (v') "->". by iApply "HΨ".
  Qed.

  Lemma close_spec ch :
    {{{ is_chan ch end_prot }}} close ch {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hch HΨ". wp_lam.
    wp_smart_apply (send1_spec0 with "[$Hch]"); eauto.
  Qed.

  Global Instance ses_prot_contractive A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) ses_prot.
  Proof. solve_contractive. Qed.
  Global Instance ses_prot_ne A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) ses_prot.
  Proof. solve_proper. Qed.
  Global Instance ses_prot_proper A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) ses_prot.
  Proof. solve_proper. Qed.

End session_proofs.

Section session_examples.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition prot_add_base p : prot :=
    ses_prot (λ (lx : loc * Z), #lx.1) (λ lx, lx.1 ↦ #lx.2)%I
      (λ lx, ses_prot (λ (_:unit), #()) (λ _, lx.1 ↦ #(lx.2 + 2))%I
                       (λ _, p)).

  Instance prot_add_base_contractive : Contractive prot_add_base.
  Proof. intros n p1 p2 Heq.
    unfold prot_add_base. apply ses_prot_ne; try done.
    intros x. eapply ses_prot_contractive; try done.
    solve_proper.
  Qed.

  Definition prog_ses_add : val :=
    λ: "<>",
      let: "c" := new #() in
      Fork (let: "r" := recv "c" in
            Fst "r" <- ((!(Fst "r") + #2));;
            let: "c" := send (Snd "r") #() in wait "c");;
      let: "l" := ref #40 in
      let: "c" := send "c" "l" in
      let: "r" := recv "c" in
      close (Snd "r");; assert: (!"l" = #42).

  Definition prot_add : prot := prot_add_base end_prot.

  Lemma prog_ses_add_spec : {{{ True }}} prog_ses_add #() {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_spec prot_add); [done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_smart_apply (recv_spec with "Hch2").
      iIntros ([l x] ch') "[Hch2 Hl]"=> /=.
      wp_load. wp_store. wp_smart_apply (send_spec () with "[$Hch2 $Hl]").
      iIntros (ch'') "Hch2". by wp_smart_apply (wait_spec with "Hch2").
    - wp_alloc l as "Hl". wp_smart_apply (send_spec (l,40%Z) with "[$Hch1 $Hl]").
      iIntros (ch') "Hch1". wp_smart_apply (recv_spec with "Hch1").
      iIntros (_ ?) "[Hch1 Hl]". wp_smart_apply (close_spec with "Hch1").
      iIntros "_". wp_smart_apply wp_assert. wp_load. wp_pures.
      iModIntro. iSplit; [done|]. by iApply "HΦ".
  Qed.

  Definition prog_add_rec : val :=
    λ: "<>",
      let: "c" := new #() in
      Fork ((rec: "go" "c" :=
             let: "r" := recv "c" in
             Fst "r" <- ((!(Fst "r") + #2));;
             let: "c" := send (Snd "r") #() in "go" "c") "c");;
      let: "l" := ref #38 in
      let: "c" := send "c" "l" in
      let: "r" := recv "c" in
      let: "c" := send (Snd "r") "l" in
      let: "r" := recv "c" in
      assert: (!"l" = #42);; Snd "r".

  Definition prot_add_rec := fixpoint prot_add_base.
  Lemma prot_add_rec_unfold : prot_add_rec ≡ prot_add_base prot_add_rec.
  Proof. rewrite /prot_add_rec. apply fixpoint_unfold. Qed.

  Lemma prog_add_rec_spec :
    {{{ True }}}
      prog_add_rec #()
    {{{ c, RET c; is_chan0 c prot_add_rec }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_spec prot_add_rec); [done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_pure _.
      iLöb as "IH" forall (ch).
      rewrite {2}prot_add_rec_unfold.
      wp_smart_apply (recv_spec with "Hch2").
      iIntros ([l x] ch') "[Hch2 Hl]"=> /=.
      wp_load. wp_store. wp_smart_apply (send_spec () with "[$Hch2 $Hl]").
      iIntros (ch'') "Hch2". do 2 wp_pure. by iApply "IH".
    - rewrite {2}prot_add_rec_unfold.
      wp_alloc l as "Hl". wp_smart_apply (send_spec (l,38%Z) with "[$Hch1 $Hl]").
      iIntros (ch') "Hch1". wp_smart_apply (recv_spec with "Hch1").
      iIntros (_ ch'') "[Hch1 Hl]"=> /=.
      replace #(38 + 2) with #40; last by do 2 f_equiv; lia.
      rewrite {2}prot_add_rec_unfold.
      wp_smart_apply (send_spec (l,40%Z) with "[$Hch1 $Hl]").
      iIntros (ch''') "Hch1". wp_smart_apply (recv_spec with "Hch1").
      iIntros (_ ?) "[Hch1 Hl]". wp_smart_apply wp_assert. wp_load. wp_pures.
      replace #(40 + 2) with #42; last by do 2 f_equiv; lia.
      iModIntro. iSplit; [done|].
      iIntros "!>". wp_pures. by iApply "HΦ".
  Qed.

End session_examples.
