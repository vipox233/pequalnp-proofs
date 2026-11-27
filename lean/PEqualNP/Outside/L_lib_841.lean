import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_841_aux

private lemma sum_choose_hockey (n t : ℕ) :
    ∑ r ∈ Finset.range (t + 1), Nat.choose (r + n) r = Nat.choose (t + n + 1) t := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : k + 1 + n = k + n + 1 := by omega
    rw [h1]
    exact (Nat.choose_succ_succ (k + n + 1) k).symm

private lemma card_edgeCounts (e : ℕ) (he : 0 < e) :
    ∀ t : ℕ, Fintype.card {m : Fin e → Fin (t + 1) // ∑ j : Fin e, (m j).val = t} =
      Nat.choose (t + e - 1) t := by
  induction e with
  | zero => exact absurd he (Nat.lt_irrefl 0)
  | succ e' ih =>
    cases e' with
    | zero =>
      intro t
      have hch : Nat.choose (t + 1 - 1) t = 1 := by simp
      rw [hch, Fintype.card_eq_one_iff]
      refine ⟨⟨fun _ => ⟨t, Nat.lt_succ_self t⟩, by simp⟩, ?_⟩
      intro m
      apply Subtype.ext
      funext j
      fin_cases j
      apply Fin.ext
      have hm := m.2
      simpa using hm
    | succ n =>
      intro t
      have he' : 0 < n + 1 := Nat.succ_pos n
      rw [← Finset.card_univ]
      have hmaps : ∀ m ∈ (Finset.univ : Finset {m : Fin (n + 2) → Fin (t + 1) // ∑ j, (m j).val = t}),
          m.1 0 ∈ (Finset.univ : Finset (Fin (t + 1))) := fun _ _ => Finset.mem_univ _
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      have hfib : ∀ k : Fin (t + 1),
          ((Finset.univ : Finset {m : Fin (n + 2) → Fin (t + 1) // ∑ j, (m j).val = t}).filter
            (fun m => m.1 0 = k)).card =
          Fintype.card {m' : Fin (n + 1) → Fin (t - k.val + 1) // ∑ j, (m' j).val = t - k.val} := by
        intro k
        rw [← Finset.card_univ]
        apply Finset.card_bij
          (fun m hm =>
            ⟨fun j => ⟨(m.1 j.succ).val, by
              have hsum := m.2
              rw [Fin.sum_univ_succ] at hsum
              have hm0 : m.1 0 = k := (Finset.mem_filter.mp hm).2
              rw [hm0] at hsum
              have hle : (m.1 j.succ).val ≤ ∑ i : Fin (n + 1), (m.1 i.succ).val :=
                Finset.single_le_sum (f := fun i : Fin (n + 1) => (m.1 i.succ).val)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
              omega⟩, by
              have hsum := m.2
              rw [Fin.sum_univ_succ] at hsum
              have hm0 : m.1 0 = k := (Finset.mem_filter.mp hm).2
              rw [hm0] at hsum
              dsimp only
              omega⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro m1 hm1 m2 hm2 heq
          have hk1 : m1.1 0 = k := (Finset.mem_filter.mp hm1).2
          have hk2 : m2.1 0 = k := (Finset.mem_filter.mp hm2).2
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ ?_ i
          · exact hk1.trans hk2.symm
          · intro j
            have hj := congrArg (fun x => (x.1 j).val) heq
            exact Fin.ext hj
        · intro m' _
          let mval : Fin (n + 2) → Fin (t + 1) :=
            Fin.cons k (fun j => ⟨(m'.1 j).val, by have := (m'.1 j).isLt; omega⟩)
          have hsum : ∑ j : Fin (n + 2), (mval j).val = t := by
            rw [Fin.sum_univ_succ]
            simp only [mval, Fin.cons_zero, Fin.cons_succ]
            have hm' := m'.2
            have hk := k.isLt
            omega
          refine ⟨⟨mval, hsum⟩, ?_, ?_⟩
          · simp [mval]
          · apply Subtype.ext
            funext j
            apply Fin.ext
            simp [mval]
      calc ∑ k : Fin (t + 1),
            ((Finset.univ : Finset {m : Fin (n + 2) → Fin (t + 1) // ∑ j, (m j).val = t}).filter
              (fun m => m.1 0 = k)).card
          = ∑ k : Fin (t + 1), Nat.choose ((t - k.val) + (n + 1) - 1) (t - k.val) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [hfib k, ih he' (t - k.val)]
        _ = ∑ r ∈ Finset.range (t + 1), Nat.choose (r + n) r := by
              apply Finset.sum_bij (fun k _ => t - k.val)
              · intro k _; rw [Finset.mem_range]; omega
              · intro k1 _ k2 _ heq
                apply Fin.ext
                have h1 := k1.isLt; have h2 := k2.isLt; omega
              · intro r hr
                rw [Finset.mem_range] at hr
                refine ⟨⟨t - r, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
              · intro k _
                rfl
        _ = Nat.choose (t + n + 1) t := sum_choose_hockey n t
        _ = Nat.choose (t + (n + 2) - 1) t := rfl

private lemma card_multinomial_finset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset β) :
    ∀ (A : Finset α) (c : β → ℕ), (∑ b ∈ B, c b = A.card) →
      Fintype.card { f : ↥A → ↥B // ∀ b : ↥B, (Finset.univ.filter (fun a : ↥A => f a = b)).card = c b.1 } *
        (∏ b ∈ B, (c b).factorial) = A.card.factorial := by
  classical
  refine Finset.induction_on B ?_ ?_
  · intro A c hsum
    simp only [Finset.sum_empty] at hsum
    have hA0 : A.card = 0 := hsum.symm
    have hAempty : A = ∅ := Finset.card_eq_zero.mp hA0
    rw [Finset.prod_empty, mul_one, hA0, Nat.factorial_zero, Fintype.card_eq_one_iff]
    refine ⟨⟨fun a => absurd (by rw [← hAempty]; exact a.2) (Finset.notMem_empty _),
      fun b => absurd b.2 (Finset.notMem_empty _)⟩, ?_⟩
    intro f
    apply Subtype.ext
    funext a
    exact absurd (by rw [← hAempty]; exact a.2) (Finset.notMem_empty _)
  · intro b0 B' hb0 ih A c hsum
    rw [Finset.sum_insert hb0] at hsum
    rw [Finset.prod_insert hb0]
    let k := c b0
    have hk_le : k ≤ A.card := by omega
    let Full := { f : ↥A → ↥(insert b0 B') //
      ∀ b : ↥(insert b0 B'), (Finset.univ.filter (fun a : ↥A => f a = b)).card = c b.1 }
    let preimg : Full → Finset α := fun f =>
      (Finset.univ.filter (fun a : ↥A => (f.1 a).1 = b0)).image Subtype.val
    have hmaps : ∀ f ∈ (Finset.univ : Finset Full), preimg f ∈ A.powersetCard k := by
      intro f _
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
        exact a.2
      · rw [Finset.card_image_of_injective _ Subtype.val_injective]
        have hfb0 := f.2 ⟨b0, Finset.mem_insert_self b0 B'⟩
        have hfeq : Finset.univ.filter (fun a : ↥A => (f.1 a).1 = b0) =
            Finset.univ.filter (fun a : ↥A => f.1 a = ⟨b0, Finset.mem_insert_self b0 B'⟩) := by
          ext a; simp [Subtype.ext_iff]
        rw [hfeq, hfb0]
    have hfib_card : ∀ T ∈ A.powersetCard k,
        ((Finset.univ : Finset Full).filter (fun f => preimg f = T)).card =
        Fintype.card { g : ↥(A \ T) → ↥B' //
          ∀ b : ↥B', (Finset.univ.filter (fun a : ↥(A \ T) => g a = b)).card = c b.1 } := by
      intro T hT
      have hTsub : T ⊆ A := (Finset.mem_powersetCard.mp hT).1
      have hTcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
      rw [← Finset.card_univ]
      apply Finset.card_bij
        (fun f hf =>
          ⟨fun a =>
            have haA : a.1 ∈ A := (Finset.mem_sdiff.mp a.2).1
            have haT : a.1 ∉ T := (Finset.mem_sdiff.mp a.2).2
            have hne : (f.1 ⟨a.1, haA⟩).1 ≠ b0 := by
              intro heq
              have hmem : a.1 ∈ preimg f :=
                Finset.mem_image.mpr ⟨⟨a.1, haA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩, rfl⟩
              rw [(Finset.mem_filter.mp hf).2] at hmem
              exact haT hmem
            ⟨(f.1 ⟨a.1, haA⟩).1, (Finset.mem_insert.mp (f.1 ⟨a.1, haA⟩).2).resolve_left hne⟩, by
            intro b
            have hb_ne : b.1 ≠ b0 := fun h => hb0 (h ▸ b.2)
            have hfb := f.2 ⟨b.1, Finset.mem_insert_of_mem b.2⟩
            rw [← hfb]
            apply Finset.card_bij (fun a _ => ⟨a.1, (Finset.mem_sdiff.mp a.2).1⟩)
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff] at ha ⊢
              exact ha
            · intro a1 _ a2 _ heq
              exact Subtype.ext (congrArg (fun x : ↥A => x.1) heq)
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff] at ha
              have haT : a.1 ∉ T := by
                intro hmem
                rw [← (Finset.mem_filter.mp hf).2] at hmem
                rcases Finset.mem_image.mp hmem with ⟨a', ha', heq⟩
                have haeq : a' = a := Subtype.ext heq
                rw [haeq] at ha'
                have hb0eq : (f.1 a).1 = b0 := (Finset.mem_filter.mp ha').2
                exact hb_ne (ha.symm.trans hb0eq)
              refine ⟨⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, haT⟩⟩, ?_, Subtype.ext rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff]
              exact ha⟩)
      · intro _ _; exact Finset.mem_univ _
      · intro f1 hf1 f2 hf2 heq
        have hT1 : preimg f1 = T := (Finset.mem_filter.mp hf1).2
        have hT2 : preimg f2 = T := (Finset.mem_filter.mp hf2).2
        apply Subtype.ext
        funext a
        apply Subtype.ext
        by_cases haT : a.1 ∈ T
        · have h1 : (f1.1 a).1 = b0 := by
            rw [← hT1] at haT
            rcases Finset.mem_image.mp haT with ⟨a', ha', heqa⟩
            have : a' = a := Subtype.ext heqa
            rw [this] at ha'
            exact (Finset.mem_filter.mp ha').2
          have h2 : (f2.1 a).1 = b0 := by
            rw [← hT2] at haT
            rcases Finset.mem_image.mp haT with ⟨a', ha', heqa⟩
            have : a' = a := Subtype.ext heqa
            rw [this] at ha'
            exact (Finset.mem_filter.mp ha').2
          exact h1.trans h2.symm
        · exact congrArg (fun g => (g.1 ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, haT⟩⟩).1) heq
      · intro g _
        let fval : ↥A → ↥(insert b0 B') := fun a =>
          if ha : a.1 ∈ T then ⟨b0, Finset.mem_insert_self b0 B'⟩
          else ⟨(g.1 ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, ha⟩⟩).1,
            Finset.mem_insert_of_mem (g.1 ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, ha⟩⟩).2⟩
        have hfcond : ∀ b : ↥(insert b0 B'),
            (Finset.univ.filter (fun a : ↥A => fval a = b)).card = c b.1 := by
          intro b
          by_cases hbb0 : b.1 = b0
          · rw [hbb0]
            change _ = k
            rw [← hTcard]
            apply Finset.card_bij (fun a _ => a.1)
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff, fval] at ha
              by_cases haT : a.1 ∈ T
              · exact haT
              · simp only [haT, ↓reduceDIte] at ha
                have hmemB' := (g.1 ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, haT⟩⟩).2
                rw [ha, hbb0] at hmemB'
                exact absurd hmemB' hb0
            · intro a1 _ a2 _ heq; exact Subtype.ext heq
            · intro x hx
              refine ⟨⟨x, hTsub hx⟩, ?_, rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff, fval, hx, ↓reduceDIte]
              exact hbb0.symm
          · have hbB' : b.1 ∈ B' := (Finset.mem_insert.mp b.2).resolve_left hbb0
            rw [← g.2 ⟨b.1, hbB'⟩]
            apply Finset.card_bij (fun a ha =>
              ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, by
                intro haT
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff, fval, haT, ↓reduceDIte] at ha
                exact hbb0 ha.symm⟩⟩)
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff, fval] at ha ⊢
              split_ifs at ha with haT
              · exact absurd ha.symm hbb0
              · exact ha
            · intro a1 _ a2 _ heq; exact Subtype.ext (congrArg (fun x : ↥(A \ T) => x.1) heq)
            · intro a ha
              have haA : a.1 ∈ A := (Finset.mem_sdiff.mp a.2).1
              have haT : a.1 ∉ T := (Finset.mem_sdiff.mp a.2).2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff] at ha
              refine ⟨⟨a.1, haA⟩, ?_, Subtype.ext rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff, fval, haT, ↓reduceDIte]
              exact ha
        refine ⟨⟨fval, hfcond⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          ext x
          simp only [preimg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, fval]
          constructor
          · rintro ⟨a, ha, rfl⟩
            by_cases haT : a.1 ∈ T
            · exact haT
            · simp only [haT, ↓reduceDIte] at ha
              have hmemB' := (g.1 ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, haT⟩⟩).2
              rw [ha] at hmemB'
              exact absurd hmemB' hb0
          · intro hx
            refine ⟨⟨x, hTsub hx⟩, ?_, rfl⟩
            simp [hx]
        · apply Subtype.ext
          funext a
          apply Subtype.ext
          have haT : a.1 ∉ T := (Finset.mem_sdiff.mp a.2).2
          simp [fval, haT]
    have hcard_eq : Fintype.card Full =
        ∑ T ∈ A.powersetCard k,
          Fintype.card { g : ↥(A \ T) → ↥B' //
            ∀ b : ↥B', (Finset.univ.filter (fun a : ↥(A \ T) => g a = b)).card = c b.1 } := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
      exact Finset.sum_congr rfl (fun T hT => hfib_card T hT)
    have hstep : Fintype.card Full * (∏ b ∈ B', (c b).factorial) =
        A.card.choose k * (A.card - k).factorial := by
      rw [hcard_eq, Finset.sum_mul]
      have hterm : ∀ T ∈ A.powersetCard k,
          Fintype.card { g : ↥(A \ T) → ↥B' //
            ∀ b : ↥B', (Finset.univ.filter (fun a : ↥(A \ T) => g a = b)).card = c b.1 } *
            (∏ b ∈ B', (c b).factorial) = (A.card - k).factorial := by
        intro T hT
        have hTsub : T ⊆ A := (Finset.mem_powersetCard.mp hT).1
        have hTcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
        have hsdiff : (A \ T).card = A.card - k := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub, hTcard]
        have hsum' : ∑ b ∈ B', c b = (A \ T).card := by omega
        rw [ih (A \ T) c hsum', hsdiff]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    calc Fintype.card Full * (k.factorial * ∏ b ∈ B', (c b).factorial)
        = (Fintype.card Full * ∏ b ∈ B', (c b).factorial) * k.factorial := by ring
      _ = (A.card.choose k * (A.card - k).factorial) * k.factorial := by rw [hstep]
      _ = A.card.choose k * k.factorial * (A.card - k).factorial := by ring
      _ = A.card.factorial := Nat.choose_mul_factorial_mul_factorial hk_le

private lemma card_multinomial_div {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (c : β → ℕ) (hsum : ∑ b ∈ B, c b = A.card) :
    Fintype.card { f : ↥A → ↥B // ∀ b : ↥B, (Finset.univ.filter (fun a : ↥A => f a = b)).card = c b.1 } =
      A.card.factorial / (∏ b ∈ B, (c b).factorial) := by
  have hmul := card_multinomial_finset B A c hsum
  have hpos : 0 < ∏ b ∈ B, (c b).factorial :=
    Finset.prod_pos (fun b _ => Nat.factorial_pos (c b))
  exact (Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt hpos) hmul)

end PEqualNP.Outside.L_lib_841_aux

open PEqualNP.Outside.L_lib_841_aux

theorem PEqualNP.Outside.L_lib_841 :
    (∀ (s e t : ℕ), 0 < e →
  ∀ (src dst : Fin e → Fin s) (w : Fin e → ℕ)
    (initial : (Fin t → Fin s) → ℕ) (wanted : Fin s → ℕ),
  let multiplicity := fun (v : Fin t → Fin s) (i : Fin s) =>
    (Finset.univ.filter (fun j => v j = i)).card
  let edgeCounts := {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t}
  let marginal := fun (endpoint : Fin e → Fin s) (m : edgeCounts) (i : Fin s) =>
    ∑ j ∈ Finset.univ.filter (fun l => endpoint l = i), (m.val j).val
  let prior := fun (a : Fin s → ℕ) =>
    ∑ v : Fin t → Fin s, if multiplicity v = a then initial v else 0
  let ways := fun (m : edgeCounts) =>
    ∏ i : Fin s, (marginal src m i).factorial /
      (∏ j ∈ Finset.univ.filter (fun l => src l = i), ((m.val j).val).factorial)
  Nat.card edgeCounts = Nat.choose (t+e-1) t ∧
    (∑ p : Fin t → Fin e,
      if multiplicity (dst ∘ p) = wanted
      then initial (src ∘ p) * ∏ j, w (p j) else 0) =
    ∑ m : edgeCounts, if marginal dst m = wanted
      then prior (marginal src m) * ways m * ∏ j, (w j)^((m.val j).val) else 0) := by
  intro s e t he src dst w initial wanted
  dsimp only
  let multiplicity : (Fin t → Fin s) → Fin s → ℕ :=
    fun v i => (Finset.univ.filter (fun j => v j = i)).card
  let edgeCounts := {m : Fin e → Fin (t + 1) // ∑ j, (m j).val = t}
  let marginal : (Fin e → Fin s) → edgeCounts → Fin s → ℕ :=
    fun endpoint m i => ∑ j ∈ Finset.univ.filter (fun l => endpoint l = i), (m.val j).val
  let prior : (Fin s → ℕ) → ℕ :=
    fun a => ∑ v : Fin t → Fin s, if multiplicity v = a then initial v else 0
  let ways : edgeCounts → ℕ :=
    fun m => ∏ i : Fin s, (marginal src m i).factorial /
      (∏ j ∈ Finset.univ.filter (fun l => src l = i), ((m.val j).val).factorial)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact card_edgeCounts e he t
  · let hist : (Fin t → Fin e) → edgeCounts := fun p =>
      ⟨fun l => ⟨(Finset.univ.filter (fun j : Fin t => p j = l)).card,
          Nat.lt_succ_of_le (by simpa using Finset.card_le_univ (Finset.univ.filter (fun j : Fin t => p j = l)))⟩,
        by
          have h := Finset.card_eq_sum_card_fiberwise (f := p)
            (s := (Finset.univ : Finset (Fin t))) (t := (Finset.univ : Finset (Fin e)))
            (fun _ _ => Finset.mem_univ _)
          simpa using h.symm⟩
    have hmarg_hist : ∀ (endpoint : Fin e → Fin s) (p : Fin t → Fin e),
        marginal endpoint (hist p) = multiplicity (endpoint ∘ p) := by
      intro endpoint p
      funext i
      dsimp only [marginal, hist, multiplicity, Function.comp]
      have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin t)).filter (fun j => endpoint (p j) = i),
          p j ∈ (Finset.univ : Finset (Fin e)).filter (fun l => endpoint l = i) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hli : endpoint l = i := (Finset.mem_filter.mp hl).2
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hpj => ⟨by rw [hpj, hli], hpj⟩, fun h => h.2⟩
    have hprod_hist : ∀ p : Fin t → Fin e,
        (∏ j : Fin t, w (p j)) = ∏ l : Fin e, (w l) ^ ((hist p).val l).val := by
      intro p
      have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin t)), p j ∈ (Finset.univ : Finset (Fin e)) :=
        fun _ _ => Finset.mem_univ _
      rw [← Finset.prod_fiberwise_of_maps_to hmaps]
      refine Finset.prod_congr rfl (fun l _ => ?_)
      have hconst : ∏ j ∈ Finset.univ.filter (fun j : Fin t => p j = l), w (p j) =
          ∏ _j ∈ Finset.univ.filter (fun j : Fin t => p j = l), w l :=
        Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2])
      rw [hconst, Finset.prod_const]
    have hfiber_ways : ∀ (m : edgeCounts) (v : Fin t → Fin s),
        multiplicity v = marginal src m →
        ((Finset.univ : Finset (Fin t → Fin e)).filter (fun p => hist p = m ∧ src ∘ p = v)).card =
          ways m := by
      intro m v hv
      let Pos : Fin s → Finset (Fin t) := fun i => Finset.univ.filter (fun j => v j = i)
      let Out : Fin s → Finset (Fin e) := fun i => Finset.univ.filter (fun l => src l = i)
      let Local : Fin s → Type := fun i =>
        { f : ↥(Pos i) → ↥(Out i) //
          ∀ l : ↥(Out i), (Finset.univ.filter (fun j : ↥(Pos i) => f j = l)).card = (m.val l.1).val }
      have hbij : ((Finset.univ : Finset (Fin t → Fin e)).filter (fun p => hist p = m ∧ src ∘ p = v)).card =
          Fintype.card ((i : Fin s) → Local i) := by
        rw [← Finset.card_univ]
        apply Finset.card_bij
          (fun p hp => fun i =>
            have hpm : hist p = m := (Finset.mem_filter.mp hp).2.1
            have hpv : src ∘ p = v := (Finset.mem_filter.mp hp).2.2
            ⟨fun j => ⟨p j.1, by
              simp only [Out, Finset.mem_filter, Finset.mem_univ, true_and]
              have hvj : v j.1 = i := (Finset.mem_filter.mp j.2).2
              exact (congrFun hpv j.1).trans hvj⟩, by
              intro l
              have hml : (Finset.univ.filter (fun j : Fin t => p j = l.1)).card = (m.val l.1).val := by
                have := congrArg (fun x : edgeCounts => (x.val l.1).val) hpm
                simpa [hist] using this
              rw [← hml]
              apply Finset.card_bij (fun j _ => j.1)
              · intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff] at hj ⊢
                exact hj
              · intro j1 _ j2 _ heq; exact Subtype.ext heq
              · intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                have hjPos : j ∈ Pos i := by
                  simp only [Pos, Finset.mem_filter, Finset.mem_univ, true_and]
                  have hsl : src l.1 = i := (Finset.mem_filter.mp l.2).2
                  rw [← congrFun hpv j, Function.comp_apply, hj, hsl]
                refine ⟨⟨j, hjPos⟩, ?_, rfl⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff]
                exact hj⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 heq
          have hpv1 : src ∘ p1 = v := (Finset.mem_filter.mp hp1).2.2
          have hpv2 : src ∘ p2 = v := (Finset.mem_filter.mp hp2).2.2
          funext j
          have hjPos : j ∈ Pos (v j) := by simp [Pos]
          have h := congrArg (fun g : (i : Fin s) → Local i => ((g (v j)).1 ⟨j, hjPos⟩).1) heq
          exact h
        · intro g _
          let p : Fin t → Fin e := fun j => ((g (v j)).1 ⟨j, by simp [Pos]⟩).1
          have hpv : src ∘ p = v := by
            funext j
            have hmem := ((g (v j)).1 ⟨j, by simp [Pos]⟩).2
            exact (Finset.mem_filter.mp hmem).2
          have hpm : hist p = m := by
            apply Subtype.ext
            funext l
            apply Fin.ext
            dsimp only [hist]
            let i := src l
            have hlOut : l ∈ Out i := by simp [Out, i]
            rw [← (g i).2 ⟨l, hlOut⟩]
            apply Finset.card_bij (fun j hj =>
              ⟨j, by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                simp only [Pos, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [← congrFun hpv j, Function.comp_apply, hj]⟩)
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff] at hj ⊢
              have hvj : v j = i := by
                rw [← congrFun hpv j, Function.comp_apply, hj]
              dsimp only [p] at hj
              have hcast : ∀ (i1 i2 : Fin s) (h : i1 = i2) (hj1 : j ∈ Pos i1) (hj2 : j ∈ Pos i2),
                  ((g i1).1 ⟨j, hj1⟩).1 = ((g i2).1 ⟨j, hj2⟩).1 := by
                intro i1 i2 h; subst h; intro _ _; rfl
              rw [← hcast (v j) i hvj (by simp [Pos]) _]
              exact hj
            · intro j1 _ j2 _ heq; exact congrArg Subtype.val heq
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff] at hj
              have hvj : v j.1 = i := (Finset.mem_filter.mp j.2).2
              refine ⟨j.1, ?_, Subtype.ext rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              dsimp only [p]
              have hcast : ∀ (i1 i2 : Fin s) (h : i1 = i2) (hj1 : j.1 ∈ Pos i1) (hj2 : j.1 ∈ Pos i2),
                  ((g i1).1 ⟨j.1, hj1⟩).1 = ((g i2).1 ⟨j.1, hj2⟩).1 := by
                intro i1 i2 h; subst h; intro _ _; rfl
              rw [hcast (v j.1) i hvj (by simp [Pos]) j.2]
              exact hj
          refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpm, hpv⟩, ?_⟩
          funext i
          apply Subtype.ext
          funext j
          apply Subtype.ext
          have hvj : v j.1 = i := (Finset.mem_filter.mp j.2).2
          dsimp only [p]
          have hcast : ∀ (i1 i2 : Fin s) (h : i1 = i2) (hj1 : j.1 ∈ Pos i1) (hj2 : j.1 ∈ Pos i2),
              ((g i1).1 ⟨j.1, hj1⟩).1 = ((g i2).1 ⟨j.1, hj2⟩).1 := by
            intro i1 i2 h; subst h; intro _ _; rfl
          exact hcast (v j.1) i hvj (by simp [Pos]) j.2
      rw [hbij, Fintype.card_pi]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hsum_i : ∑ l ∈ Out i, (m.val l).val = (Pos i).card := by
        have hi := congrFun hv i
        simpa [Pos, Out, multiplicity, marginal] using hi.symm
      have hdiv := card_multinomial_div (Pos i) (Out i) (fun l => (m.val l).val) hsum_i
      have hpos_eq : (Pos i).card = marginal src m i := by
        have hi := congrFun hv i
        simpa [Pos, multiplicity] using hi
      rw [hdiv, hpos_eq]
    have hmaps_hist : ∀ p ∈ (Finset.univ : Finset (Fin t → Fin e)), hist p ∈ (Finset.univ : Finset edgeCounts) :=
      fun _ _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps_hist]
    change (∑ m : edgeCounts, ∑ p ∈ Finset.univ.filter (fun p : Fin t → Fin e => hist p = m),
      if multiplicity (dst ∘ p) = wanted then initial (src ∘ p) * ∏ j, w (p j) else 0) =
      ∑ m : edgeCounts, if marginal dst m = wanted
        then prior (marginal src m) * ways m * ∏ j, (w j) ^ ((m.val j).val) else 0
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hdst : marginal dst m = wanted
    · simp only [hdst, ↓reduceIte]
      have hinner : ∑ p ∈ Finset.univ.filter (fun p : Fin t → Fin e => hist p = m),
          (if multiplicity (dst ∘ p) = wanted then initial (src ∘ p) * ∏ j, w (p j) else 0) =
          (∑ p ∈ Finset.univ.filter (fun p : Fin t → Fin e => hist p = m), initial (src ∘ p)) *
            ∏ j, (w j) ^ ((m.val j).val) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have hpm : hist p = m := (Finset.mem_filter.mp hp).2
        rw [← hmarg_hist dst p, hpm, hdst]
        simp only [↓reduceIte, hprod_hist p, hpm]
      rw [hinner]
      congr 1
      have hmaps_src : ∀ p ∈ Finset.univ.filter (fun p : Fin t → Fin e => hist p = m),
          src ∘ p ∈ (Finset.univ : Finset (Fin t → Fin s)) := fun _ _ => Finset.mem_univ _
      rw [← Finset.sum_fiberwise_of_maps_to hmaps_src]
      dsimp only [prior]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hconst : ∑ p ∈ (Finset.univ.filter (fun p : Fin t → Fin e => hist p = m)).filter (fun p => src ∘ p = v),
          initial (src ∘ p) =
          ((Finset.univ.filter (fun p : Fin t → Fin e => hist p = m ∧ src ∘ p = v)).card) * initial v := by
        have hfeq : (Finset.univ.filter (fun p : Fin t → Fin e => hist p = m)).filter (fun p => src ∘ p = v) =
            Finset.univ.filter (fun p : Fin t → Fin e => hist p = m ∧ src ∘ p = v) := by
          ext p; simp
        rw [hfeq]
        calc ∑ p ∈ Finset.univ.filter (fun p : Fin t → Fin e => hist p = m ∧ src ∘ p = v), initial (src ∘ p)
            = ∑ _p ∈ Finset.univ.filter (fun p : Fin t → Fin e => hist p = m ∧ src ∘ p = v), initial v :=
                Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2.2])
          _ = _ := by rw [Finset.sum_const, smul_eq_mul]
      rw [hconst]
      by_cases hv : multiplicity v = marginal src m
      · simp only [hv, ↓reduceIte]
        rw [hfiber_ways m v hv, Nat.mul_comm]
      · simp only [hv, ↓reduceIte, zero_mul]
        have hempty : Finset.univ.filter (fun p : Fin t → Fin e => hist p = m ∧ src ∘ p = v) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p _ ⟨hpm, hpv⟩
          apply hv
          rw [← hpv, ← hmarg_hist src p, hpm]
        rw [hempty, Finset.card_empty, zero_mul]
    · simp only [hdst, ↓reduceIte]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have hpm : hist p = m := (Finset.mem_filter.mp hp).2
      rw [← hmarg_hist dst p, hpm]
      simp only [hdst, ↓reduceIte]
