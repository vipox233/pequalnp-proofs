import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_621_aux

private lemma card_mod_two_of_involution {β : Type} [DecidableEq β]
    (P : Finset β) (ι : β → β)
    (hmem : ∀ x ∈ P, ι x ∈ P) (hinvol : ∀ x ∈ P, ι (ι x) = x) :
    P.card % 2 = (P.filter (fun x => ι x = x)).card % 2 := by
  have hmove_even : ∀ (k : ℕ) (M : Finset β), M.card = k →
      (∀ x ∈ M, ι x ∈ M) → (∀ x ∈ M, ι (ι x) = x) → (∀ x ∈ M, ι x ≠ x) →
      M.card % 2 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro M hcard hm hi hne
      by_cases hemp : M = ∅
      · subst hemp; simp
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hix : ι x ∈ M := hm x hx
        have hxne : ι x ≠ x := hne x hx
        let M' := (M.erase x).erase (ι x)
        have hM'sub : M' ⊆ M := fun y hy =>
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
        have hix_mem : ι x ∈ M.erase x := Finset.mem_erase.mpr ⟨hxne, hix⟩
        have hcard' : M'.card + 2 = M.card := by
          have h1 : (M.erase x).card + 1 = M.card := Finset.card_erase_add_one hx
          have h2 : M'.card + 1 = (M.erase x).card := Finset.card_erase_add_one hix_mem
          omega
        have hm' : ∀ y ∈ M', ι y ∈ M' := by
          intro y hy
          have hy1 : y ≠ ι x := (Finset.mem_erase.mp hy).1
          have hy2 : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
          have hyM : y ∈ M := hM'sub hy
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hm y hyM⟩⟩
          · intro h
            apply hy2
            have := congrArg ι h
            rwa [hi y hyM, hi x hx] at this
          · intro h
            apply hy1
            have := congrArg ι h
            rwa [hi y hyM] at this
        have hev := ih M'.card (by omega) M' rfl hm' (fun y hy => hi y (hM'sub hy))
          (fun y hy => hne y (hM'sub hy))
        omega
  let Fix := P.filter (fun x => ι x = x)
  let Move := P.filter (fun x => ι x ≠ x)
  have hsplit : P.card = Fix.card + Move.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
    congr 1
    ext x
    simp only [Fix, Move, Finset.mem_union, Finset.mem_filter]
    tauto
  have hM_mem : ∀ x ∈ Move, ι x ∈ Move := by
    intro x hx
    simp only [Move, Finset.mem_filter] at hx ⊢
    refine ⟨hmem x hx.1, ?_⟩
    intro h
    apply hx.2
    have := congrArg ι h
    rw [hinvol x hx.1] at this
    exact this
  have hM_inv : ∀ x ∈ Move, ι (ι x) = x := fun x hx => hinvol x (Finset.mem_filter.mp hx).1
  have hM_ne : ∀ x ∈ Move, ι x ≠ x := fun x hx => (Finset.mem_filter.mp hx).2
  have hev := hmove_even Move.card Move rfl hM_mem hM_inv hM_ne
  change P.card % 2 = Fix.card % 2
  omega

private def slotsFn {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) :
    Finset (Fin r × Finset (Fin n)) :=
  (Finset.univ : Finset (Fin r × Finset (Fin n))).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)

private def totalFn {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (table : Finset (Fin r × Finset (Fin n))) : ℕ :=
  (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card

private def coeffFn {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (M : Finset (Fin r × Finset (Fin n))) (g : ℕ → Bool) : Bool :=
  ((M.powerset.filter (fun T => g (totalFn scope U T))).card).testBit 0

private def flipSlot {n r : ℕ} (scope : Fin r → Finset (Fin n)) (v : Fin n)
    (s : Fin r × Finset (Fin n)) : Fin r × Finset (Fin n) :=
  (s.1, if v ∈ scope s.1 then symmDiff s.2 {v} else s.2)

private lemma flipSlot_invol {n r : ℕ} (scope : Fin r → Finset (Fin n)) (v : Fin n)
    (s : Fin r × Finset (Fin n)) : flipSlot scope v (flipSlot scope v s) = s := by
  rcases s with ⟨i, S⟩
  simp only [flipSlot]
  split_ifs
  · exact Prod.ext rfl (symmDiff_symmDiff_cancel_right {v} S)
  · rfl

private lemma flipSlot_inj {n r : ℕ} (scope : Fin r → Finset (Fin n)) (v : Fin n) :
    Function.Injective (flipSlot scope v) :=
  Function.LeftInverse.injective (flipSlot_invol scope v)

private lemma flipSlot_inter_of_not_mem {n r : ℕ} (scope : Fin r → Finset (Fin n))
    {U : Finset (Fin n)} {v : Fin n} (hv : v ∉ U) (s : Fin r × Finset (Fin n)) :
    (flipSlot scope v s).2 ∩ U = s.2 ∩ U := by
  simp only [flipSlot]
  split_ifs
  · ext x
    simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hx, _⟩ | ⟨rfl, _⟩, hxU⟩
      · exact ⟨hx, hxU⟩
      · exact absurd hxU hv
    · rintro ⟨hx, hxU⟩
      refine ⟨Or.inl ⟨hx, ?_⟩, hxU⟩
      intro h
      exact hv (h ▸ hxU)
  · rfl

private lemma flipSlot_mem_slots {n r : ℕ} (scope : Fin r → Finset (Fin n))
    {V : Finset (Fin n)} {v : Fin n} (hv : v ∈ V)
    {s : Fin r × Finset (Fin n)} (hs : s ∈ slotsFn scope V) :
    flipSlot scope v s ∈ slotsFn scope V := by
  simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and, flipSlot] at hs ⊢
  split_ifs with hvs
  · intro x hx
    simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hx
    rcases hx with ⟨hxs, _⟩ | ⟨rfl, _⟩
    · exact hs hxs
    · exact Finset.mem_inter.mpr ⟨hvs, hv⟩
  · exact hs

private lemma flipWord_inter_scope {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (v : Fin n) (x : Finset (Fin n)) (i : Fin r) :
    (symmDiff x {v}) ∩ scope i = (flipSlot scope v (i, x ∩ scope i)).2 := by
  simp only [flipSlot]
  split_ifs with hvs
  · ext y
    simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hyv : y = v
    · subst hyv
      simp [hvs]
    · simp [hyv]
  · ext y
    simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hyv : y = v
    · subst hyv
      simp [hvs]
    · simp [hyv]

private lemma totalFn_flipTable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    {V : Finset (Fin n)} {v : Fin n} (hv : v ∈ V)
    (T : Finset (Fin r × Finset (Fin n))) :
    totalFn scope V (T.image (flipSlot scope v)) = totalFn scope V T := by
  unfold totalFn
  refine Finset.card_bij (fun x _ => symmDiff x {v})
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hx ⊢
      refine ⟨?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hy
        rcases hy with ⟨hyx, _⟩ | ⟨rfl, _⟩
        · exact hx.1 hyx
        · exact hv
      · intro i
        have hi := hx.2 i
        rw [Finset.mem_image] at hi
        obtain ⟨t, htT, hteq⟩ := hi
        have hts : t = flipSlot scope v (i, x ∩ scope i) := by
          rw [← hteq, flipSlot_invol]
        rw [flipWord_inter_scope]
        change flipSlot scope v (i, x ∩ scope i) ∈ T
        exact hts ▸ htT)
    (fun x1 _ x2 _ heq => by
      have := congrArg (fun S => symmDiff S {v}) heq
      simpa only [symmDiff_symmDiff_cancel_right] using this)
    (fun y hy => by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hy
      refine ⟨symmDiff y {v}, ?_, symmDiff_symmDiff_cancel_right {v} y⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hz
        rcases hz with ⟨hzy, _⟩ | ⟨rfl, _⟩
        · exact hy.1 hzy
        · exact hv
      · intro i
        rw [flipWord_inter_scope]
        exact Finset.mem_image.mpr ⟨(i, y ∩ scope i), hy.2 i, rfl⟩)

private lemma step_elim {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (v : Fin n) (hv : v ∉ U)
    (A : Finset (Fin r × Finset (Fin n))) (hA : A ⊆ slotsFn scope U)
    (g : ℕ → Bool) :
    let V := insert v U
    let liftUV := (slotsFn scope V).filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    coeffFn scope V liftUV g = coeffFn scope U A (fun c => g (2 * c)) := by
  intro V liftUV
  have hvV : v ∈ V := Finset.mem_insert_self v U
  have hUV : U ⊆ V := Finset.subset_insert v U
  let flipT : Finset (Fin r × Finset (Fin n)) → Finset (Fin r × Finset (Fin n)) :=
    fun T => T.image (flipSlot scope v)
  have hflipT_invol : ∀ T, flipT (flipT T) = T := by
    intro T
    ext s
    simp only [flipT, Finset.mem_image]
    constructor
    · rintro ⟨t, ⟨u, hu, rfl⟩, rfl⟩
      rwa [flipSlot_invol]
    · intro hs
      exact ⟨flipSlot scope v s, ⟨s, hs, rfl⟩, flipSlot_invol scope v s⟩
  let P := liftUV.powerset.filter (fun T => g (totalFn scope V T))
  have hP_mem : ∀ T ∈ P, flipT T ∈ P := by
    intro T hT
    simp only [P, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [flipT, Finset.mem_image] at hs
      obtain ⟨t, htT, rfl⟩ := hs
      have htL : t ∈ liftUV := hT.1 htT
      simp only [liftUV, Finset.mem_filter] at htL ⊢
      refine ⟨flipSlot_mem_slots scope hvV htL.1, ?_⟩
      change (t.1, (flipSlot scope v t).2 ∩ U) ∈ A
      rw [flipSlot_inter_of_not_mem scope hv t]
      exact htL.2
    · rw [totalFn_flipTable scope hvV T]
      exact hT.2
  have hmod := card_mod_two_of_involution P flipT hP_mem (fun T _ => hflipT_invol T)
  let pull : Finset (Fin r × Finset (Fin n)) → Finset (Fin r × Finset (Fin n)) :=
    fun B => (slotsFn scope V).filter (fun s => (s.1, s.2 ∩ U) ∈ B)
  have hpull_total : ∀ B : Finset (Fin r × Finset (Fin n)),
      totalFn scope V (pull B) = 2 * totalFn scope U B := by
    intro B
    unfold totalFn
    have hbij : (V.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ pull B)).card =
        ((Finset.univ : Finset Bool) ×ˢ
          (U.powerset.filter (fun y => ∀ i : Fin r, (i, y ∩ scope i) ∈ B))).card := by
      refine Finset.card_bij (fun x _ => (decide (v ∈ x), x ∩ U))
        (fun x hx => by
          simp only [Finset.mem_filter, Finset.mem_powerset] at hx
          rw [Finset.mem_product]
          refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩⟩
          intro i
          have hi := hx.2 i
          simp only [pull, Finset.mem_filter] at hi
          have heq : (x ∩ U) ∩ scope i = (x ∩ scope i) ∩ U := by
            ext z; simp [and_left_comm, and_comm]
          rw [heq]
          exact hi.2)
        (fun x1 hx1 x2 hx2 heq => by
          simp only [Finset.mem_filter, Finset.mem_powerset] at hx1 hx2
          have hv_iff : v ∈ x1 ↔ v ∈ x2 := by
            have h1 := congrArg Prod.fst heq
            simpa only [decide_eq_decide] using h1
          have hinter : x1 ∩ U = x2 ∩ U := congrArg Prod.snd heq
          ext z
          by_cases hzv : z = v
          · subst hzv; exact hv_iff
          · have h1 : z ∈ x1 → z ∈ U := fun hz => by
              have hzV := hx1.1 hz
              simp only [V, Finset.mem_insert] at hzV
              exact hzV.resolve_left hzv
            have h2 : z ∈ x2 → z ∈ U := fun hz => by
              have hzV := hx2.1 hz
              simp only [V, Finset.mem_insert] at hzV
              exact hzV.resolve_left hzv
            constructor
            · intro hz1
              have hz1' : z ∈ x1 ∩ U := Finset.mem_inter.mpr ⟨hz1, h1 hz1⟩
              rw [hinter] at hz1'
              exact (Finset.mem_inter.mp hz1').1
            · intro hz2
              have hz2' : z ∈ x2 ∩ U := Finset.mem_inter.mpr ⟨hz2, h2 hz2⟩
              rw [← hinter] at hz2'
              exact (Finset.mem_inter.mp hz2').1)
        (fun byp hbyp => by
          rw [Finset.mem_product] at hbyp
          rcases byp with ⟨b, y⟩
          have hy := hbyp.2
          simp only [Finset.mem_filter, Finset.mem_powerset] at hy
          let x := if b then insert v y else y
          have hxv : v ∈ x ↔ b = true := by
            dsimp only [x]
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte, iff_false]
              exact fun h => hv (hy.1 h)
            · simp
          have hxU : x ∩ U = y := by
            dsimp only [x]
            cases b
            · simp [Finset.inter_eq_left.mpr hy.1]
            · simp only [↓reduceIte]
              ext z
              simp only [Finset.mem_inter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hzy, hzU⟩
                · exact absurd hzU hv
                · exact hzy
              · intro hzy
                exact ⟨Or.inr hzy, hy.1 hzy⟩
          have hxV : x ⊆ V := by
            dsimp only [x]
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact hy.1.trans hUV
            · simp only [↓reduceIte]
              intro z hz
              simp only [Finset.mem_insert] at hz
              rcases hz with rfl | hzy
              · exact hvV
              · exact hUV (hy.1 hzy)
          refine ⟨x, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨hxV, ?_⟩
            intro i
            simp only [pull, Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and]
              intro z hz
              simp only [Finset.mem_inter] at hz ⊢
              exact ⟨hz.2, hxV hz.1⟩
            · have heq : (x ∩ scope i) ∩ U = y ∩ scope i := by
                rw [← hxU]
                ext z; simp [and_left_comm, and_comm]
              rw [heq]
              exact hy.2 i
          · exact Prod.ext (by simp [hxv]) hxU)
    rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  have hfix_card : (P.filter (fun T => flipT T = T)).card =
      (A.powerset.filter (fun B => g (2 * totalFn scope U B))).card := by
    refine (Finset.card_bij (fun B _ => pull B)
      (fun B hB => by
        simp only [Finset.mem_filter, Finset.mem_powerset] at hB
        simp only [P, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro s hs
          simp only [pull, liftUV, Finset.mem_filter] at hs ⊢
          exact ⟨hs.1, hB.1 hs.2⟩
        · rw [hpull_total B]
          exact hB.2
        · ext s
          simp only [flipT, Finset.mem_image]
          constructor
          · rintro ⟨t, ht, rfl⟩
            simp only [pull, Finset.mem_filter] at ht ⊢
            refine ⟨flipSlot_mem_slots scope hvV ht.1, ?_⟩
            change (t.1, (flipSlot scope v t).2 ∩ U) ∈ B
            rw [flipSlot_inter_of_not_mem scope hv t]
            exact ht.2
          · intro hs
            refine ⟨flipSlot scope v s, ?_, flipSlot_invol scope v s⟩
            simp only [pull, Finset.mem_filter] at hs ⊢
            refine ⟨flipSlot_mem_slots scope hvV hs.1, ?_⟩
            change (s.1, (flipSlot scope v s).2 ∩ U) ∈ B
            rw [flipSlot_inter_of_not_mem scope hv s]
            exact hs.2)
      (fun B1 hB1 B2 hB2 heq => by
        simp only [Finset.mem_filter, Finset.mem_powerset] at hB1 hB2
        ext s
        have hmem_self : ∀ (B : Finset (Fin r × Finset (Fin n))), B ⊆ A → s ∈ B → s ∈ pull B := by
          intro B hBA hsB
          have hsU : s ∈ slotsFn scope U := hA (hBA hsB)
          simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsU
          have hs_subU : s.2 ⊆ U := fun z hz => (Finset.mem_inter.mp (hsU hz)).2
          have hs_inter : s.2 ∩ U = s.2 := Finset.inter_eq_left.mpr hs_subU
          simp only [pull, slotsFn, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun z hz => ?_, ?_⟩
          · have h1 := Finset.mem_inter.mp (hsU hz)
            exact Finset.mem_inter.mpr ⟨h1.1, hUV h1.2⟩
          · rw [hs_inter]
            exact hsB
        constructor
        · intro hs1
          have hs2 : s ∈ pull B2 := heq ▸ hmem_self B1 hB1.1 hs1
          simp only [pull, Finset.mem_filter] at hs2
          have hsU : s ∈ slotsFn scope U := hA (hB1.1 hs1)
          simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsU
          have hs_inter : s.2 ∩ U = s.2 := Finset.inter_eq_left.mpr (fun z hz => (Finset.mem_inter.mp (hsU hz)).2)
          rw [hs_inter] at hs2
          exact hs2.2
        · intro hs2
          have hs1 : s ∈ pull B1 := heq.symm ▸ hmem_self B2 hB2.1 hs2
          simp only [pull, Finset.mem_filter] at hs1
          have hsU : s ∈ slotsFn scope U := hA (hB2.1 hs2)
          simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsU
          have hs_inter : s.2 ∩ U = s.2 := Finset.inter_eq_left.mpr (fun z hz => (Finset.mem_inter.mp (hsU hz)).2)
          rw [hs_inter] at hs1
          exact hs1.2)
      (fun T hT => by
        simp only [P, Finset.mem_filter, Finset.mem_powerset] at hT
        let B := T.image (fun s => (s.1, s.2 ∩ U))
        have hBA : B ⊆ A := by
          intro s hs
          simp only [B, Finset.mem_image] at hs
          obtain ⟨t, htT, rfl⟩ := hs
          exact (Finset.mem_filter.mp (hT.1.1 htT)).2
        have hpull_eq : pull B = T := by
          ext s
          constructor
          · intro hs
            simp only [pull, Finset.mem_filter, B, Finset.mem_image] at hs
            obtain ⟨hsV, t, htT, hteq⟩ := hs
            have htV : t ∈ slotsFn scope V := (Finset.mem_filter.mp (hT.1.1 htT)).1
            have h1 : t.1 = s.1 := (Prod.mk.inj hteq).1
            have h2 : t.2 ∩ U = s.2 ∩ U := (Prod.mk.inj hteq).2
            simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsV htV
            by_cases hsame : v ∈ s.2 ↔ v ∈ t.2
            · have hseq : s = t := by
                apply Prod.ext h1.symm
                ext z
                by_cases hzv : z = v
                · subst hzv; exact hsame
                · have hsz : z ∈ s.2 → z ∈ U := fun hz =>
                    (Finset.mem_insert.mp (Finset.mem_inter.mp (hsV hz)).2).resolve_left hzv
                  have htz : z ∈ t.2 → z ∈ U := fun hz =>
                    (Finset.mem_insert.mp (Finset.mem_inter.mp (htV hz)).2).resolve_left hzv
                  constructor
                  · intro hz
                    have hz' : z ∈ s.2 ∩ U := Finset.mem_inter.mpr ⟨hz, hsz hz⟩
                    rw [← h2] at hz'
                    exact (Finset.mem_inter.mp hz').1
                  · intro hz
                    have hz' : z ∈ t.2 ∩ U := Finset.mem_inter.mpr ⟨hz, htz hz⟩
                    rw [h2] at hz'
                    exact (Finset.mem_inter.mp hz').1
              exact hseq ▸ htT
            · have hv_scope : v ∈ scope t.1 := by
                by_cases hvs : v ∈ s.2
                · have := (Finset.mem_inter.mp (hsV hvs)).1
                  rwa [← h1] at this
                · have hvt : v ∈ t.2 := by tauto
                  exact (Finset.mem_inter.mp (htV hvt)).1
              have hs_flip : s = flipSlot scope v t := by
                apply Prod.ext
                · exact h1.symm
                · simp only [flipSlot, hv_scope, ↓reduceIte]
                  ext z
                  simp only [Finset.mem_symmDiff, Finset.mem_singleton]
                  by_cases hzv : z = v
                  · subst hzv
                    tauto
                  · have hsz : z ∈ s.2 → z ∈ U := fun hz =>
                      (Finset.mem_insert.mp (Finset.mem_inter.mp (hsV hz)).2).resolve_left hzv
                    have htz : z ∈ t.2 → z ∈ U := fun hz =>
                      (Finset.mem_insert.mp (Finset.mem_inter.mp (htV hz)).2).resolve_left hzv
                    constructor
                    · intro hz
                      have hz' : z ∈ s.2 ∩ U := Finset.mem_inter.mpr ⟨hz, hsz hz⟩
                      rw [← h2] at hz'
                      exact Or.inl ⟨(Finset.mem_inter.mp hz').1, hzv⟩
                    · rintro (⟨hz, _⟩ | ⟨rfl, _⟩)
                      · have hz' : z ∈ t.2 ∩ U := Finset.mem_inter.mpr ⟨hz, htz hz⟩
                        rw [h2] at hz'
                        exact (Finset.mem_inter.mp hz').1
                      · exact absurd rfl hzv
              rw [← hT.2, hs_flip]
              exact Finset.mem_image.mpr ⟨t, htT, rfl⟩
          · intro hs
            have hsV : s ∈ slotsFn scope V := (Finset.mem_filter.mp (hT.1.1 hs)).1
            simp only [pull, Finset.mem_filter]
            exact ⟨hsV, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
        refine ⟨B, ?_, hpull_eq⟩
        simp only [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨hBA, ?_⟩
        rw [← hpull_total B, hpull_eq]
        exact hT.1.2)).symm
  unfold coeffFn
  change P.card.testBit 0 = ((A.powerset.filter (fun B => g (2 * totalFn scope U B))).card).testBit 0
  rw [Nat.testBit_zero, Nat.testBit_zero, hmod, hfix_card]

private lemma multi_elim {n r : ℕ} (scope : Fin r → Finset (Fin n)) :
    ∀ (k : ℕ) (V U : Finset (Fin n)), U ⊆ V → (V \ U).card = k →
      ∀ (A : Finset (Fin r × Finset (Fin n))), A ⊆ slotsFn scope U →
        ∀ g : ℕ → Bool,
          coeffFn scope V ((slotsFn scope V).filter (fun s => (s.1, s.2 ∩ U) ∈ A)) g =
            coeffFn scope U A (fun c => g (2 ^ k * c)) := by
  intro k
  induction k with
  | zero =>
    intro V U hUV hcard A hA g
    have hVU : V = U := by
      have hemp : V \ U = ∅ := Finset.card_eq_zero.mp hcard
      exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hemp) hUV
    subst hVU
    have hfilt : (slotsFn scope V).filter (fun s => (s.1, s.2 ∩ V) ∈ A) = A := by
      ext s
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hsV, hsA⟩
        simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsV
        have hi : s.2 ∩ V = s.2 := Finset.inter_eq_left.mpr (fun z hz => (Finset.mem_inter.mp (hsV hz)).2)
        rwa [hi] at hsA
      · intro hsA
        have hsV := hA hsA
        refine ⟨hsV, ?_⟩
        simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsV
        have hi : s.2 ∩ V = s.2 := Finset.inter_eq_left.mpr (fun z hz => (Finset.mem_inter.mp (hsV hz)).2)
        rwa [hi]
    rw [hfilt]
    simp [coeffFn]
  | succ k ih =>
    intro V U hUV hcard A hA g
    have hne : (V \ U).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hne
    have hvV : v ∈ V := (Finset.mem_sdiff.mp hv).1
    have hvU : v ∉ U := (Finset.mem_sdiff.mp hv).2
    let U' := insert v U
    have hU'V : U' ⊆ V := Finset.insert_subset hvV hUV
    have hcard' : (V \ U').card = k := by
      have hsd : V \ U' = (V \ U).erase v := by
        ext z
        simp only [U', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [hsd]
      have := Finset.card_erase_add_one hv
      omega
    let A' := (slotsFn scope U').filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    have hA' : A' ⊆ slotsFn scope U' := Finset.filter_subset _ _
    have hlift_eq : (slotsFn scope V).filter (fun s => (s.1, s.2 ∩ U) ∈ A) =
        (slotsFn scope V).filter (fun s => (s.1, s.2 ∩ U') ∈ A') := by
      ext s
      simp only [A', Finset.mem_filter]
      constructor
      · rintro ⟨hsV, hsA⟩
        refine ⟨hsV, ?_, ?_⟩
        · simp only [slotsFn, Finset.mem_filter, Finset.mem_univ, true_and] at hsV ⊢
          intro z hz
          simp only [Finset.mem_inter] at hz ⊢
          exact ⟨(Finset.mem_inter.mp (hsV hz.1)).1, hz.2⟩
        · have hi : (s.2 ∩ U') ∩ U = s.2 ∩ U := by
            ext z
            simp only [U', Finset.mem_inter, Finset.mem_insert]
            tauto
          rwa [hi]
      · rintro ⟨hsV, _, hsA⟩
        refine ⟨hsV, ?_⟩
        have hi : (s.2 ∩ U') ∩ U = s.2 ∩ U := by
          ext z
          simp only [U', Finset.mem_inter, Finset.mem_insert]
          tauto
        rwa [hi] at hsA
    rw [hlift_eq, ih V U' hU'V hcard' A' hA' g]
    have hstep := step_elim scope U v hvU A hA (fun c => g (2 ^ k * c))
    dsimp only at hstep
    rw [hstep]
    have hpow : (fun c => g (2 ^ k * (2 * c))) = (fun c => g (2 ^ (k + 1) * c)) := by
      funext c
      congr 1
      ring
    rw [hpow]

end PEqualNP.Outside.L_lib_621_aux

theorem PEqualNP.Outside.L_lib_621 : ∀ (n r : Nat) (scope : Fin r → Finset (Fin n)),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let all := (Finset.univ : Finset Site)
  let slots := fun U : Finset Site => (Finset.univ : Finset Slot).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)
  let total := fun (U : Finset Site) (table : Finset Slot) =>
    (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (U : Finset Site) (M : Finset Slot) (g : Nat → Bool) =>
    ((M.powerset.filter (fun T => g (total U T))).card).testBit 0
  ∀ (U : Finset Site) (A : Finset Slot), A ⊆ slots U →
    let lift := (slots all).filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    ∀ g : Nat → Bool, coeff all lift g =
      coeff U A (fun c => g (2^(n-U.card)*c)) := by
  intro n r scope Site Slot all slots total coeff U A hA lift g
  have hcard : (all \ U).card = n - U.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  exact PEqualNP.Outside.L_lib_621_aux.multi_elim scope (n - U.card) all U
    (Finset.subset_univ U) hcard A hA g
