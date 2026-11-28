import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_426_aux

open Finset

section Trace

variable {K : Type} [Field K] {n k : ℕ}

def trace (width : ℕ → ℕ)
    (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (off : List (List K) → ℕ → K) (x : Fin n → K) (u : Fin k → K) :
    ℕ → List (List K)
  | 0 => []
  | d + 1 =>
    let h := trace width ask off x u d
    h ++ [List.ofFn (fun j : Fin (width d) => ask h j.val (x, u) + off h j.val)]

lemma trace_length (width : ℕ → ℕ)
    (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (off : List (List K) → ℕ → K) (x : Fin n → K) (u : Fin k → K) :
    ∀ d, (trace width ask off x u d).length = d
  | 0 => rfl
  | d + 1 => by simp [trace, trace_length width ask off x u d]

lemma foldl_range_eq_trace (width : ℕ → ℕ)
    (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (off : List (List K) → ℕ → K) (x : Fin n → K) (u : Fin k → K) :
    ∀ r, (List.range r).foldl (fun (h : List (List K)) (s : ℕ) =>
      h ++ [List.ofFn (fun j : Fin (width s) => ask h j.val (x, u) + off h j.val)]) [] =
      trace width ask off x u r
  | 0 => rfl
  | r + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_range_eq_trace width ask off x u r]
    rfl

lemma trace_take (width : ℕ → ℕ)
    (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (off : List (List K) → ℕ → K) (x : Fin n → K) (u : Fin k → K) :
    ∀ {r d}, d ≤ r → (trace width ask off x u r).take d = trace width ask off x u d
  | 0, d, hd => by
    have hd0 : d = 0 := by omega
    subst hd0
    rfl
  | r + 1, d, hd => by
    by_cases hdr : d = r + 1
    · subst hdr
      exact List.take_of_length_le (by rw [trace_length])
    · have hle : d ≤ r := by omega
      change (trace width ask off x u r ++
        [List.ofFn (fun j : Fin (width r) =>
          ask (trace width ask off x u r) j.val (x, u) + off (trace width ask off x u r) j.val)]).take d = _
      rw [List.take_append_of_le_length (by rw [trace_length]; exact hle)]
      exact trace_take width ask off x u hle

end Trace

section LinearAlgebraHelpers

lemma affine_dir_finrank_lt {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {A B : AffineSubspace K V}
    (hAne : (A : Set V).Nonempty) (hAB : A < B) :
    Module.finrank K A.direction < Module.finrank K B.direction := by
  have hle : A.direction ≤ B.direction := AffineSubspace.direction_le hAB.le
  have hlt : A.direction < B.direction := by
    refine lt_of_le_of_ne hle fun heq => hAB.ne ?_
    obtain ⟨a, ha⟩ := hAne
    have haB : a ∈ B := hAB.le ha
    ext v
    constructor
    · intro hv; exact hAB.le hv
    · intro hv
      have hsub : v -ᵥ a ∈ B.direction := AffineSubspace.vsub_mem_direction hv haB
      rw [← heq] at hsub
      simpa using AffineSubspace.vadd_mem_of_mem_direction hsub ha
  exact Submodule.finrank_lt_finrank_of_lt hlt

lemma dual_decomp_inf {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {A B : Submodule K W} {φ : W →ₗ[K] K} (hker : A ⊓ B ≤ LinearMap.ker φ) :
    ∃ φA φB : W →ₗ[K] K, A ≤ LinearMap.ker φA ∧ B ≤ LinearMap.ker φB ∧ φ = φA + φB := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A ⊔ B)
  obtain ⟨B', hB'⟩ := Submodule.exists_isCompl (B.comap (A ⊔ B).subtype)
  have hAB_inj : ∀ (a : A) (b : B), (a : W) + (b : W) = 0 → φ a = 0 := by
    intro a b hab
    have haB : (a : W) ∈ B := by
      have : (a : W) = -(b : W) := eq_neg_of_add_eq_zero_left hab
      rw [this]; exact B.neg_mem b.2
    exact hker ⟨a.2, haB⟩
  let fAB : ↥(A ⊔ B) →ₗ[K] K :=
    { toFun := fun z =>
        let h := Submodule.mem_sup.1 z.2
        φ h.choose
      map_add' := fun z1 z2 => by
        have h1 := Submodule.mem_sup.1 z1.2
        have h2 := Submodule.mem_sup.1 z2.2
        have h12 := Submodule.mem_sup.1 (z1 + z2).2
        set a1 := h1.choose; have ha1 := h1.choose_spec.1
        set b1 := h1.choose_spec.2.choose; have hb1 := h1.choose_spec.2.choose_spec.1
        have he1 := h1.choose_spec.2.choose_spec.2
        set a2 := h2.choose; have ha2 := h2.choose_spec.1
        set b2 := h2.choose_spec.2.choose; have hb2 := h2.choose_spec.2.choose_spec.1
        have he2 := h2.choose_spec.2.choose_spec.2
        set a12 := h12.choose; have ha12 := h12.choose_spec.1
        set b12 := h12.choose_spec.2.choose; have hb12 := h12.choose_spec.2.choose_spec.1
        have he12 := h12.choose_spec.2.choose_spec.2
        have hsum : (a12 - (a1 + a2)) + (b12 - (b1 + b2)) = 0 := by
          have : (a12 + b12) = (a1 + b1) + (a2 + b2) := by
            rw [he12, Submodule.coe_add, ← he1, ← he2]
          calc (a12 - (a1 + a2)) + (b12 - (b1 + b2))
              = (a12 + b12) - ((a1 + b1) + (a2 + b2)) := by abel
            _ = 0 := sub_eq_zero.2 this
        have h0 := hAB_inj ⟨a12 - (a1 + a2), A.sub_mem ha12 (A.add_mem ha1 ha2)⟩
          ⟨b12 - (b1 + b2), B.sub_mem hb12 (B.add_mem hb1 hb2)⟩ hsum
        simp only [map_sub, map_add, sub_eq_zero] at h0
        exact h0
      map_smul' := fun c z => by
        have h1 := Submodule.mem_sup.1 z.2
        have hc := Submodule.mem_sup.1 (c • z).2
        set a1 := h1.choose; have ha1 := h1.choose_spec.1
        set b1 := h1.choose_spec.2.choose; have hb1 := h1.choose_spec.2.choose_spec.1
        have he1 := h1.choose_spec.2.choose_spec.2
        set ac := hc.choose; have hac := hc.choose_spec.1
        set bc := hc.choose_spec.2.choose; have hbc := hc.choose_spec.2.choose_spec.1
        have hec := hc.choose_spec.2.choose_spec.2
        have hsum : (ac - c • a1) + (bc - c • b1) = 0 := by
          have : ac + bc = c • (a1 + b1) := by
            rw [hec, Submodule.coe_smul_of_tower, ← he1]
          calc (ac - c • a1) + (bc - c • b1)
              = (ac + bc) - c • (a1 + b1) := by rw [smul_add]; abel
            _ = 0 := sub_eq_zero.2 this
        have h0 := hAB_inj ⟨ac - c • a1, A.sub_mem hac (A.smul_mem c ha1)⟩
          ⟨bc - c • b1, B.sub_mem hbc (B.smul_mem c hb1)⟩ hsum
        simp only [map_sub, map_smul, sub_eq_zero, RingHom.id_apply] at h0
        exact h0 }
  have hfA : ∀ a (ha : a ∈ A), fAB ⟨a, Submodule.mem_sup_left ha⟩ = φ a := by
    intro a ha
    dsimp only [fAB]
    let z : ↥(A ⊔ B) := ⟨a, Submodule.mem_sup_left ha⟩
    have h := Submodule.mem_sup.1 z.2
    set a' := h.choose; have ha' := h.choose_spec.1
    set b' := h.choose_spec.2.choose; have hb' := h.choose_spec.2.choose_spec.1
    have he' := h.choose_spec.2.choose_spec.2
    have hsum : (a' - a) + b' = 0 := by
      calc (a' - a) + b' = (a' + b') - a := by abel
        _ = 0 := sub_eq_zero.2 he'
    have h0 := hAB_inj ⟨a' - a, A.sub_mem ha' ha⟩ ⟨b', hb'⟩ hsum
    simp only [map_sub, sub_eq_zero] at h0
    exact h0
  have hfB : ∀ b (hb : b ∈ B), fAB ⟨b, Submodule.mem_sup_right hb⟩ = 0 := by
    intro b hb
    dsimp only [fAB]
    let z : ↥(A ⊔ B) := ⟨b, Submodule.mem_sup_right hb⟩
    have h := Submodule.mem_sup.1 z.2
    set a' := h.choose; have ha' := h.choose_spec.1
    set b' := h.choose_spec.2.choose; have hb' := h.choose_spec.2.choose_spec.1
    have he' := h.choose_spec.2.choose_spec.2
    have hsum : a' + (b' - b) = 0 := by
      calc a' + (b' - b) = (a' + b') - b := by abel
        _ = 0 := sub_eq_zero.2 he'
    exact hAB_inj ⟨a', ha'⟩ ⟨b' - b, B.sub_mem hb' hb⟩ hsum
  let proj : W →ₗ[K] ↥(A ⊔ B) := Submodule.linearProjOfIsCompl (A ⊔ B) C hC
  let φB : W →ₗ[K] K := fAB.comp proj
  refine ⟨φ - φB, φB, ?_, ?_, by ext w; simp⟩
  · intro a ha
    have hp : proj a = ⟨a, Submodule.mem_sup_left ha⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨a, Submodule.mem_sup_left ha⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, φB, LinearMap.comp_apply]
    rw [hp, hfA a ha, sub_self]
  · intro b hb
    have hp : proj b = ⟨b, Submodule.mem_sup_right hb⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨b, Submodule.mem_sup_right hb⟩
    simp only [LinearMap.mem_ker, φB, LinearMap.comp_apply]
    rw [hp]
    exact hfB b hb

lemma dual_decomp_finset {K W ι : Type} [Field K] [AddCommGroup W] [Module K W]
    [DecidableEq ι] (s : Finset ι) (H : ι → Submodule K W) (φ : W →ₗ[K] K)
    (hker : (s.inf H) ≤ LinearMap.ker φ) :
    ∃ f : ι → W →ₗ[K] K, (∀ i ∈ s, H i ≤ LinearMap.ker (f i)) ∧ φ = ∑ i ∈ s, f i := by
  induction s using Finset.induction generalizing φ with
  | empty =>
    have h0 : φ = 0 := by
      ext w
      have hw : w ∈ (∅ : Finset ι).inf H := by simp
      exact hker hw
    exact ⟨fun _ => 0, by simp, by simp [h0]⟩
  | @insert a s ha ih =>
    rw [Finset.inf_insert] at hker
    obtain ⟨φa, φs, hφa, hφs, hsum⟩ := dual_decomp_inf hker
    obtain ⟨f, hf, hfs⟩ := ih φs hφs
    refine ⟨fun i => if i = a then φa else f i, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.1 hi with rfl | his
      · simpa using hφa
      · have hne : i ≠ a := fun h => ha (h ▸ his)
        simpa [hne] using hf i his
    · rw [sum_insert ha, if_pos rfl]
      have hrest : ∑ i ∈ s, (if i = a then φa else f i) = ∑ i ∈ s, f i :=
        sum_congr rfl fun i hi => if_neg (fun (h : i = a) => ha (h ▸ hi))
      rw [hrest, ← hfs, hsum]

lemma affine_separation {K X ι : Type} [Field K] [AddCommGroup X] [Module K X]
    [DecidableEq ι] (P : AffineSubspace K X) (s : Finset ι) (B : ι → AffineSubspace K X)
    (hdisj : ∀ x ∈ P, ∃ i ∈ s, x ∉ B i) :
    ∃ f : ι → X →ᵃ[K] K,
      (∀ i ∈ s, ∀ x ∈ B i, f i x = 0) ∧
      ∀ x ∈ P, ∑ i ∈ s, f i x = 1 := by
  classical
  by_cases hemp : ∃ i ∈ s, ¬ (B i : Set X).Nonempty
  · obtain ⟨i0, hi0, hne0⟩ := hemp
    refine ⟨fun i => if i = i0 then AffineMap.const K X (1 : K) else 0, ?_, ?_⟩
    · intro i _ x hx
      by_cases hi : i = i0
      · subst hi; exact absurd ⟨x, hx⟩ hne0
      · simp [hi]
    · intro x _
      rw [sum_eq_single i0]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd hi0 h
  push_neg at hemp
  let hom : AffineSubspace K X → Submodule K (X × K) := fun A =>
    Submodule.span K ((fun x : X => (x, (1 : K))) '' (A : Set X))
  have hhom_mem : ∀ (A : AffineSubspace K X) (x : X),
      (A : Set X).Nonempty → ((x, (1 : K)) ∈ hom A ↔ x ∈ A) := by
    intro A x hAne
    constructor
    · intro hmem
      obtain ⟨a0, ha0⟩ := hAne
      let S : Submodule K (X × K) :=
        Submodule.span K {(a0, (1 : K))} ⊔ A.direction.map (LinearMap.inl K X K)
      have hsub : hom A ≤ S := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        have hsubv : y -ᵥ a0 ∈ A.direction := AffineSubspace.vsub_mem_direction hy ha0
        have heq : (y, (1 : K)) = (a0, (1 : K)) + (y -ᵥ a0, (0 : K)) := by
          ext <;> simp [vsub_eq_sub]
        dsimp only
        rw [heq]
        exact Submodule.add_mem_sup (Submodule.subset_span (Set.mem_singleton _))
          (Submodule.mem_map_of_mem hsubv)
      have hS := hsub hmem
      obtain ⟨p1, hp1, p2, hp2, hsum⟩ := Submodule.mem_sup.1 hS
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hp1
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hp2
      have hc : c = 1 := by
        have := congrArg Prod.snd hsum
        simpa using this
      have hx_eq : x = v +ᵥ a0 := by
        have := congrArg Prod.fst hsum
        simp only [Prod.smul_fst, Prod.fst_add, LinearMap.inl_apply, hc, one_smul] at this
        rw [← this, vadd_eq_add, add_comm]
      rw [hx_eq]
      exact AffineSubspace.vadd_mem_of_mem_direction hv ha0
    · intro hx
      exact Submodule.subset_span ⟨x, hx, rfl⟩
  let H : Option ι → Submodule K (X × K)
    | none => hom P
    | some i => hom (B i)
  let sOpt : Finset (Option ι) := insert none (s.image some)
  have hker : sOpt.inf H ≤ LinearMap.ker (LinearMap.snd K X K) := by
    intro z hz
    rw [LinearMap.mem_ker, LinearMap.snd_apply]
    by_contra hz2
    have hinv : (z.2⁻¹ • z.1, (1 : K)) ∈ sOpt.inf H := by
      have heq : (z.2⁻¹ • z.1, (1 : K)) = z.2⁻¹ • z := by
        ext
        · simp
        · simp [inv_mul_cancel₀ hz2]
      rw [heq]
      exact Submodule.smul_mem _ _ hz
    have hP_ne : (P : Set X).Nonempty := by
      by_contra hPe
      have hP0 : hom P = ⊥ := by
        have : (P : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.1 hPe
        simp [hom, this]
      have hle : sOpt.inf H ≤ hom P := Finset.inf_le (mem_insert_self none _)
      rw [hP0] at hle
      have hz0 : z = 0 := (Submodule.mem_bot K).1 (hle hz)
      exact hz2 (by simp [hz0])
    have hxP : z.2⁻¹ • z.1 ∈ P := by
      have hle : sOpt.inf H ≤ hom P := Finset.inf_le (mem_insert_self none _)
      exact (hhom_mem P _ hP_ne).1 (hle hinv)
    obtain ⟨i, his, hnotB⟩ := hdisj _ hxP
    have hle : sOpt.inf H ≤ hom (B i) :=
      Finset.inf_le (mem_insert_of_mem (mem_image_of_mem some his))
    have hxB : z.2⁻¹ • z.1 ∈ B i := (hhom_mem (B i) _ (hemp i his)).1 (hle hinv)
    exact hnotB hxB
  obtain ⟨g, hg, hgsum⟩ := dual_decomp_finset sOpt H (LinearMap.snd K X K) hker
  let toAff : ((X × K) →ₗ[K] K) → (X →ᵃ[K] K) := fun ψ =>
    { toFun := fun x => ψ (x, 1)
      linear := ψ.comp (LinearMap.inl K X K)
      map_vadd' := fun p v => by
        simp only [vadd_eq_add, LinearMap.comp_apply, LinearMap.inl_apply]
        have : (v + p, (1 : K)) = (v, (0 : K)) + (p, (1 : K)) := by ext <;> simp
        rw [this, map_add] }
  refine ⟨fun i => toAff (g (some i)), ?_, ?_⟩
  · intro i his x hx
    have hle := hg (some i) (mem_insert_of_mem (mem_image_of_mem some his))
    have hmem : (x, (1 : K)) ∈ hom (B i) := Submodule.subset_span ⟨x, hx, rfl⟩
    exact hle hmem
  · intro x hx
    have h0 : g none (x, (1 : K)) = 0 := by
      have hle := hg none (mem_insert_self none _)
      exact hle (Submodule.subset_span ⟨x, hx, rfl⟩)
    have hnot : none ∉ s.image some := by simp
    rw [sum_insert hnot] at hgsum
    have heval := congrArg (fun ψ : (X × K) →ₗ[K] K => ψ (x, (1 : K))) hgsum
    simp only [LinearMap.snd_apply, LinearMap.add_apply, LinearMap.sum_apply, h0, zero_add] at heval
    rw [sum_image (fun _ _ _ _ h => Option.some.inj h)] at heval
    exact heval.symm

lemma subspace_meas_map {K U : Type} [Field K] [AddCommGroup U] [Module K U]
    [Module.Finite K U] {D E : Submodule K U} (hED : E ≤ D) :
    let d := Module.finrank K D - Module.finrank K E
    ∃ (Φ : U →ₗ[K] (Fin d → K)) (σ : (Fin d → K) →ₗ[K] U),
      (∀ w, σ w ∈ D) ∧
      (∀ w, Φ (σ w) = w) ∧
      (∀ u ∈ D, Φ u = 0 ↔ u ∈ E) := by
  classical
  intro d
  let E' : Submodule K D := E.comap D.subtype
  have hE'_rank : Module.finrank K E' = Module.finrank K E := by
    have hrange : LinearMap.range (D.subtype.domRestrict E') = E := by
      ext u
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.coe_subtype,
        Subtype.exists, Submodule.mem_comap, E']
      exact ⟨fun ⟨v, hvD, hvE, hvu⟩ => hvu ▸ hvE, fun hu => ⟨u, hED hu, hu, rfl⟩⟩
    have hinj : Function.Injective (D.subtype.domRestrict E') := fun a b h =>
      Subtype.ext (Subtype.ext h)
    rw [← hrange]
    exact (LinearEquiv.ofInjective _ hinj).finrank_eq
  have hq_rank : Module.finrank K (D ⧸ E') = d := by
    have hsum := Submodule.finrank_quotient_add_finrank E'
    rw [hE'_rank] at hsum
    have hle : Module.finrank K E ≤ Module.finrank K D := Submodule.finrank_mono hED
    omega
  let eQ : (D ⧸ E') ≃ₗ[K] (Fin d → K) :=
    LinearEquiv.ofFinrankEq (D ⧸ E') (Fin d → K) (by rw [hq_rank, Module.finrank_fin_fun])
  let πD : D →ₗ[K] (Fin d → K) := eQ.toLinearMap.comp E'.mkQ
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl D
  let Φ : U →ₗ[K] (Fin d → K) := πD.comp (Submodule.linearProjOfIsCompl D C hC)
  have hΦ_on_D : ∀ u : D, Φ u = eQ (E'.mkQ u) := fun u => by
    have hp : Submodule.linearProjOfIsCompl D C hC u = u :=
      Submodule.linearProjOfIsCompl_apply_left hC u
    change πD (Submodule.linearProjOfIsCompl D C hC u) = eQ (E'.mkQ u)
    rw [hp]
    rfl
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl E'
  have hsurj : Function.Surjective πD := eQ.surjective.comp (Submodule.mkQ_surjective E')
  have hbij : Function.Bijective (πD.comp K'.subtype) := ⟨by
    intro a b hab
    have hker : (a - b : K') ∈ LinearMap.ker (πD.comp K'.subtype) := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hab
    have hmk : E'.mkQ (a.1 - b.1) = 0 := eQ.injective (by simpa [πD] using hker)
    have hmemE : (a.1 - b.1) ∈ E' := (Submodule.Quotient.mk_eq_zero E').1 hmk
    have hmemK : (a.1 - b.1) ∈ K' := K'.sub_mem a.2 b.2
    have h0 : a.1 - b.1 = 0 := (Submodule.mem_bot K).1 (hK'.inf_eq_bot ▸ ⟨hmemE, hmemK⟩)
    exact Subtype.ext (sub_eq_zero.1 h0), by
    intro y
    obtain ⟨u, rfl⟩ := hsurj y
    obtain ⟨u1, hu1, u2, hu2, hsum⟩ := Submodule.mem_sup.1 (hK'.sup_eq_top ▸ Submodule.mem_top (x := u))
    refine ⟨⟨u2, hu2⟩, ?_⟩
    rw [← hsum]
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, πD, map_add]
    have h0 : E'.mkQ u1 = 0 := (Submodule.Quotient.mk_eq_zero E').2 hu1
    simp [h0]⟩
  let eK : K' ≃ₗ[K] (Fin d → K) := LinearEquiv.ofBijective (πD.comp K'.subtype) hbij
  let secD : (Fin d → K) →ₗ[K] D := LinearMap.comp K'.subtype eK.symm.toLinearMap
  let σ : (Fin d → K) →ₗ[K] U := D.subtype.comp secD
  refine ⟨Φ, σ, fun w => (secD w).2, fun w => ?_, fun u hu => ?_⟩
  · simp only [σ, LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hΦ_on_D]
    change πD (secD w) = w
    exact eK.apply_symm_apply w
  · rw [show Φ u = Φ (⟨u, hu⟩ : D) from rfl, hΦ_on_D]
    constructor
    · intro h0
      have hmk : E'.mkQ ⟨u, hu⟩ = 0 := eQ.injective (by simpa using h0)
      exact (Submodule.Quotient.mk_eq_zero E').1 hmk
    · intro huE
      have hmk : E'.mkQ ⟨u, hu⟩ = 0 := (Submodule.Quotient.mk_eq_zero E').2 huE
      simp [hmk]

end LinearAlgebraHelpers

section Forward

lemma greedy_prune {K V Z : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup Z] [Module K Z] [Module.Finite K Z]
    (W0 : AffineSubspace K V) (hW0 : (W0 : Set V).Nonempty)
    (ψ : V →ᵃ[K] Z) (B : V → AffineSubspace K V)
    (hmiss : ∀ v ∈ W0, ∀ v' ∈ W0, v' ∈ B v → ψ v' ≠ ψ v) :
    ∀ (s : ℕ), Module.finrank K (W0.map ψ).direction ≤ s →
      ∃ (t : ℕ) (pts : Fin t → V), 1 ≤ t ∧ t ≤ s + 1 ∧
        (∀ i : Fin t, pts i ∈ W0) ∧
        ∀ v ∈ W0, ∃ i : Fin t, v ∉ B (pts i) := by
  intro s
  induction s generalizing W0 with
  | zero =>
    intro hrank
    obtain ⟨v0, hv0⟩ := hW0
    refine ⟨1, fun _ => v0, le_rfl, le_rfl, fun _ => hv0, fun v hv => ⟨0, fun hvB => ?_⟩⟩
    have hdir0 : (W0.map ψ).direction = ⊥ :=
      Submodule.finrank_eq_zero.1 (Nat.eq_zero_of_le_zero hrank)
    have hsub : ψ v -ᵥ ψ v0 ∈ (W0.map ψ).direction :=
      AffineSubspace.vsub_mem_direction (AffineSubspace.mem_map_of_mem ψ hv)
        (AffineSubspace.mem_map_of_mem ψ hv0)
    rw [hdir0, Submodule.mem_bot] at hsub
    exact hmiss v0 hv0 v hv hvB (vsub_eq_zero_iff_eq.1 hsub)
  | succ s ih =>
    intro hrank
    obtain ⟨v0, hv0⟩ := hW0
    set W1 : AffineSubspace K V := W0 ⊓ B v0
    by_cases hW1ne : (W1 : Set V).Nonempty
    · have hlt_map : W1.map ψ < W0.map ψ := by
        have hle_map : W1.map ψ ≤ W0.map ψ := fun _ hy =>
          let ⟨v, hv, h⟩ := AffineSubspace.mem_map.1 hy
          AffineSubspace.mem_map.2 ⟨v, hv.1, h⟩
        refine lt_of_le_of_ne hle_map fun heq => ?_
        have hmem : ψ v0 ∈ W1.map ψ := by
          rw [heq]; exact AffineSubspace.mem_map_of_mem ψ hv0
        obtain ⟨v', hv', hψ⟩ := AffineSubspace.mem_map.1 hmem
        exact hmiss v0 hv0 v' hv'.1 hv'.2 hψ
      have hrank1 : Module.finrank K (W1.map ψ).direction ≤ s := by
        have hlt := affine_dir_finrank_lt (hW1ne.image ψ) hlt_map
        omega
      have hmiss1 : ∀ v ∈ W1, ∀ v' ∈ W1, v' ∈ B v → ψ v' ≠ ψ v :=
        fun v hv v' hv' hvB => hmiss v hv.1 v' hv'.1 hvB
      obtain ⟨t, pts, ht1, hts, hpts, hcov⟩ := ih W1 hW1ne hmiss1 hrank1
      refine ⟨t + 1, Fin.cons v0 pts, by omega, by omega, ?_, ?_⟩
      · intro i
        refine Fin.cases hv0 (fun j => (hpts j).1) i
      · intro v hv
        by_cases hvB : v ∈ B v0
        · obtain ⟨j, hj⟩ := hcov v ⟨hv, hvB⟩
          exact ⟨j.succ, hj⟩
        · exact ⟨0, hvB⟩
    · refine ⟨1, fun _ => v0, le_rfl, by omega, fun _ => hv0, fun v hv => ⟨0, fun hvB => ?_⟩⟩
      exact hW1ne ⟨v, hv, hvB⟩

lemma proto_to_tree {K : Type} [Field K] {n k t m r : ℕ}
    (P : AffineSubspace K (Fin n → K)) (bad : Fin m → AffineSubspace K (Fin n → K))
    (M : Fin m → (Fin k → K) →ₗ[K] (Fin t → K)) (width : ℕ → ℕ) (due : Fin m → Fin (r + 1))
    (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (off : List (List K) → ℕ → K) (out : List (List K) → Option (Fin m × (Fin t → K)))
    (hproto : ∀ x ∈ P, ∀ u : Fin k → K,
      (∃ d ≤ r, (out (trace width ask off x u d)).isSome = true) ∧
      ∀ d ≤ r, ∀ i y, out (trace width ask off x u d) = some (i, y) →
        d ≤ (due i).val ∧ x ∉ bad i ∧ y = M i u) :
    ∀ (fuel d : ℕ), d + fuel = r →
      ∀ (h : List (List K)) (Q : AffineSubspace K ((Fin n → K) × (Fin k → K))),
        h.length = d →
        (∀ j < d, out (h.take j) = none) →
        (Q : Set ((Fin n → K) × (Fin k → K))).Nonempty →
        (∀ p ∈ Q, p.1 ∈ P ∧ trace width ask off p.1 p.2 d = h) →
        ∃ (N : Finset (List ℕ)) (label : List ℕ → Fin m)
          (D E : List ℕ → Submodule K (Fin k → K)),
          let children := fun p : List ℕ => N.filter (fun q =>
            List.IsPrefix p q ∧ q.length = p.length + 1)
          [] ∈ N ∧
          D [] = Q.direction.comap (LinearMap.inr K (Fin n → K) (Fin k → K)) ∧
          (∀ p ∈ N, p.length ≤ fuel ∧ ∀ j ≤ p.length, p.take j ∈ N) ∧
          (∀ p ∈ N, (children p).Nonempty → E p ≤ D p ∧
            ((children p).card - 1) + (Module.finrank K (D p) - Module.finrank K (E p)) ≤
              width (d + p.length) ∧
            ∀ q ∈ children p, D q = E p) ∧
          (∀ p ∈ N, children p = ∅ →
            d + p.length ≤ (due (label p)).val ∧ D p ≤ LinearMap.ker (M (label p))) ∧
          ∀ x : Fin n → K, (∃ u, (x, u) ∈ Q) →
            ∃ p ∈ N, children p = ∅ ∧ x ∉ bad (label p) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro d hdr h Q hlen hprev hQne hQtr
    have hd_eq : d = r := by omega
    rw [hd_eq] at hlen hprev hQtr ⊢
    cases hout : out h with
    | none =>
      obtain ⟨⟨x, u⟩, hxu⟩ := hQne
      have ⟨hxP, htr⟩ := hQtr (x, u) hxu
      obtain ⟨d', hd'le, hd'some⟩ := (hproto x hxP u).1
      by_cases hlt : d' < r
      · have htake : trace width ask off x u d' = h.take d' := by
          rw [← htr, trace_take width ask off x u hd'le]
        rw [htake, hprev d' hlt] at hd'some
        simp at hd'some
      · have heq : d' = r := by omega
        subst heq
        rw [htr, hout] at hd'some
        simp at hd'some
    | some iy =>
      obtain ⟨i, y⟩ := iy
      refine ⟨{[]}, fun _ => i,
        fun _ => Q.direction.comap (LinearMap.inr K (Fin n → K) (Fin k → K)),
        fun _ => ⊥,
        mem_singleton_self _, rfl, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [mem_singleton.1 hp]
        refine ⟨le_rfl, fun j hj => ?_⟩
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0
        exact mem_singleton_self _
      · intro p hp hne
        rw [mem_singleton.1 hp] at hne
        obtain ⟨q, hq⟩ := hne
        simp only [mem_filter, mem_singleton] at hq
        obtain ⟨rfl, _, hlenq⟩ := hq
        simp at hlenq
      · intro p hp _
        rw [mem_singleton.1 hp]
        obtain ⟨⟨x, u⟩, hxu⟩ := hQne
        have ⟨hxP, htr⟩ := hQtr (x, u) hxu
        have hok := (hproto x hxP u).2 r le_rfl i y (by rw [htr, hout])
        refine ⟨by simpa using hok.1, ?_⟩
        intro w hw
        have hmem : (x, u + w) ∈ Q := by
          have : (x, u + w) = ((0 : Fin n → K), w) +ᵥ (x, u) := by ext <;> simp [vadd_eq_add, add_comm]
          rw [this]
          exact AffineSubspace.vadd_mem_of_mem_direction hw hxu
        have ⟨_, htr2⟩ := hQtr (x, u + w) hmem
        have hok2 := (hproto x hxP (u + w)).2 r le_rfl i y (by rw [htr2, hout])
        rw [LinearMap.mem_ker]
        have : M i (u + w) = M i u := by rw [← hok2.2.2, hok.2.2]
        rw [map_add] at this
        exact add_left_cancel (this.trans (add_zero _).symm)
      · intro x ⟨u, hxu⟩
        have ⟨hxP, htr⟩ := hQtr (x, u) hxu
        have hok := (hproto x hxP u).2 r le_rfl i y (by rw [htr, hout])
        refine ⟨[], mem_singleton_self _, ?_, hok.2.1⟩
        ext q; simp only [mem_filter, mem_singleton, notMem_empty, iff_false, not_and]
        rintro rfl _ hlenq; simp at hlenq
  | succ fuel ih =>
    intro d hdr h Q hlen hprev hQne hQtr
    cases hout : out h with
    | some iy =>
      obtain ⟨i, y⟩ := iy
      refine ⟨{[]}, fun _ => i,
        fun _ => Q.direction.comap (LinearMap.inr K (Fin n → K) (Fin k → K)),
        fun _ => ⊥,
        mem_singleton_self _, rfl, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [mem_singleton.1 hp]
        refine ⟨Nat.zero_le _, fun j hj => ?_⟩
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0
        exact mem_singleton_self _
      · intro p hp hne
        rw [mem_singleton.1 hp] at hne
        obtain ⟨q, hq⟩ := hne
        simp only [mem_filter, mem_singleton] at hq
        obtain ⟨rfl, _, hlenq⟩ := hq
        simp at hlenq
      · intro p hp _
        rw [mem_singleton.1 hp]
        obtain ⟨⟨x, u⟩, hxu⟩ := hQne
        have ⟨hxP, htr⟩ := hQtr (x, u) hxu
        have hok := (hproto x hxP u).2 d (by omega) i y (by rw [htr, hout])
        refine ⟨by simpa using hok.1, ?_⟩
        intro w hw
        have hmem : (x, u + w) ∈ Q := by
          have : (x, u + w) = ((0 : Fin n → K), w) +ᵥ (x, u) := by ext <;> simp [vadd_eq_add, add_comm]
          rw [this]
          exact AffineSubspace.vadd_mem_of_mem_direction hw hxu
        have ⟨_, htr2⟩ := hQtr (x, u + w) hmem
        have hok2 := (hproto x hxP (u + w)).2 d (by omega) i y (by rw [htr2, hout])
        rw [LinearMap.mem_ker]
        have : M i (u + w) = M i u := by rw [← hok2.2.2, hok.2.2]
        rw [map_add] at this
        exact add_left_cancel (this.trans (add_zero _).symm)
      · intro x ⟨u, hxu⟩
        have ⟨hxP, htr⟩ := hQtr (x, u) hxu
        have hok := (hproto x hxP u).2 d (by omega) i y (by rw [htr, hout])
        refine ⟨[], mem_singleton_self _, ?_, hok.2.1⟩
        ext q; simp only [mem_filter, mem_singleton, notMem_empty, iff_false, not_and]
        rintro rfl _ hlenq; simp at hlenq
    | none =>
      let X := Fin n → K
      let U := Fin k → K
      let L : (X × U) →ₗ[K] (Fin (width d) → K) :=
        LinearMap.pi (fun j : Fin (width d) => ask h j.val)
      let cOff : Fin (width d) → K := fun j => off h j.val
      let qAff : (X × U) →ᵃ[K] (Fin (width d) → K) :=
        { toFun := fun p => L p + cOff
          linear := L
          map_vadd' := fun p v => by simp [vadd_eq_add, map_add]; abel }
      let V : Submodule K (X × U) := Q.direction
      let D0 : Submodule K U := V.comap (LinearMap.inr K X U)
      let LU : U →ₗ[K] (Fin (width d) → K) := L.comp (LinearMap.inr K X U)
      let E0 : Submodule K U := D0 ⊓ LinearMap.ker LU
      let Rtot : Submodule K (Fin (width d) → K) := V.map L
      let RU : Submodule K (Fin (width d) → K) := D0.map LU
      have hRU_le : RU ≤ Rtot := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨(0, w), hw, rfl⟩
      have hrank_U : Module.finrank K D0 - Module.finrank K E0 = Module.finrank K RU := by
        have h1 := LinearMap.finrank_range_add_finrank_ker (LU.domRestrict D0)
        have hrange : LinearMap.range (LU.domRestrict D0) = RU := by
          ext y
          simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists,
            Submodule.mem_map, RU]
          exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
        have hker : Module.finrank K (LinearMap.ker (LU.domRestrict D0)) = Module.finrank K E0 := by
          have hr : LinearMap.range (D0.subtype.domRestrict (LinearMap.ker (LU.domRestrict D0))) = E0 := by
            ext w
            simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.coe_subtype,
              Subtype.exists, LinearMap.mem_ker, Submodule.mem_inf, E0]
            exact ⟨fun ⟨w', hwD, hwK, hww⟩ => hww ▸ ⟨hwD, hwK⟩,
              fun ⟨hwD, hwK⟩ => ⟨w, hwD, hwK, rfl⟩⟩
          have hinj : Function.Injective (D0.subtype.domRestrict (LinearMap.ker (LU.domRestrict D0))) :=
            fun a b hab => Subtype.ext (Subtype.ext hab)
          rw [← hr]
          exact (LinearEquiv.ofInjective _ hinj).finrank_eq
        rw [hrange, hker] at h1
        have hle : Module.finrank K E0 ≤ Module.finrank K D0 := Submodule.finrank_mono inf_le_left
        omega
      let s : ℕ := Module.finrank K Rtot - Module.finrank K RU
      have hs_width : s + (Module.finrank K D0 - Module.finrank K E0) ≤ width d := by
        have hle1 : Module.finrank K RU ≤ Module.finrank K Rtot := Submodule.finrank_mono hRU_le
        have hle2 : Module.finrank K Rtot ≤ width d := by
          calc Module.finrank K Rtot ≤ Module.finrank K (Fin (width d) → K) :=
                Submodule.finrank_le Rtot
            _ = width d := Module.finrank_fin_fun K
        omega
      let Qslice : (X × U) → AffineSubspace K (X × U) := fun p0 =>
        Q ⊓ AffineSubspace.comap qAff (AffineSubspace.mk' (qAff p0) ⊥)
      have hQslice_mem : ∀ p0 ∈ Q, p0 ∈ Qslice p0 := fun p0 hp0 =>
        ⟨hp0, by simp [AffineSubspace.mem_comap]⟩
      have hQslice_dir : ∀ p0 ∈ Q,
          (Qslice p0).direction.comap (LinearMap.inr K X U) = E0 := by
        intro p0 hp0
        have hne : ((Qslice p0 : Set (X × U))).Nonempty := ⟨p0, hQslice_mem p0 hp0⟩
        have hdir : (Qslice p0).direction = V ⊓ LinearMap.ker L := by
          ext v
          constructor
          · intro hv
            have hpv : v +ᵥ p0 ∈ Qslice p0 :=
              AffineSubspace.vadd_mem_of_mem_direction hv (hQslice_mem p0 hp0)
            have hvV : v ∈ V := by simpa using AffineSubspace.vsub_mem_direction hpv.1 hp0
            refine ⟨hvV, ?_⟩
            have hq : qAff (v +ᵥ p0) = qAff p0 := by
              have h1 : qAff (v +ᵥ p0) -ᵥ qAff p0 ∈ (⊥ : Submodule K (Fin (width d) → K)) := hpv.2
              exact vsub_eq_zero_iff_eq.1 ((Submodule.mem_bot K).1 h1)
            rw [qAff.map_vadd] at hq
            have : L v + qAff p0 = 0 + qAff p0 := by simpa [vadd_eq_add] using hq
            exact add_right_cancel this
          · rintro ⟨hvV, hvK⟩
            have hpv : v +ᵥ p0 ∈ Qslice p0 := by
              refine ⟨AffineSubspace.vadd_mem_of_mem_direction hvV hp0, ?_⟩
              show qAff (v +ᵥ p0) -ᵥ qAff p0 ∈ (⊥ : Submodule K (Fin (width d) → K))
              rw [Submodule.mem_bot, vsub_eq_zero_iff_eq, qAff.map_vadd]
              change L v + qAff p0 = qAff p0
              rw [LinearMap.mem_ker.1 hvK, zero_add]
            simpa using AffineSubspace.vsub_mem_direction hpv (hQslice_mem p0 hp0)
        rw [hdir]
        ext w
        simp [D0, E0, LU]
      have hsub_ih : ∀ p0 : {p0 : X × U // p0 ∈ Q},
          ∃ (N' : Finset (List ℕ)) (label' : List ℕ → Fin m)
            (D' E' : List ℕ → Submodule K U),
            let children' := fun p : List ℕ => N'.filter (fun q =>
              List.IsPrefix p q ∧ q.length = p.length + 1)
            [] ∈ N' ∧
            D' [] = E0 ∧
            (∀ p ∈ N', p.length ≤ fuel ∧ ∀ j ≤ p.length, p.take j ∈ N') ∧
            (∀ p ∈ N', (children' p).Nonempty → E' p ≤ D' p ∧
              ((children' p).card - 1) + (Module.finrank K (D' p) - Module.finrank K (E' p)) ≤
                width (d + 1 + p.length) ∧
              ∀ q ∈ children' p, D' q = E' p) ∧
            (∀ p ∈ N', children' p = ∅ →
              d + 1 + p.length ≤ (due (label' p)).val ∧ D' p ≤ LinearMap.ker (M (label' p))) ∧
            ∀ x : X, (∃ u, (x, u) ∈ Qslice p0.1) →
              ∃ p ∈ N', children' p = ∅ ∧ x ∉ bad (label' p) := by
        intro ⟨p0, hp0⟩
        let h' := h ++ [List.ofFn (fun j : Fin (width d) => ask h j.val p0 + off h j.val)]
        have hlen' : h'.length = d + 1 := by simp [h', hlen]
        have hprev' : ∀ j < d + 1, out (h'.take j) = none := by
          intro j hj
          by_cases hjd : j = d
          · subst j
            have : h'.take d = h := by
              rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
            rw [this, hout]
          · have hlt : j < d := by omega
            have : h'.take j = h.take j :=
              List.take_append_of_le_length (by omega)
            rw [this]
            exact hprev j hlt
        have htr' : ∀ p ∈ Qslice p0, p.1 ∈ P ∧ trace width ask off p.1 p.2 (d + 1) = h' := by
          intro p hp
          have ⟨hxP, htrp⟩ := hQtr p hp.1
          refine ⟨hxP, ?_⟩
          change trace width ask off p.1 p.2 d ++
            [List.ofFn (fun j : Fin (width d) =>
              ask (trace width ask off p.1 p.2 d) j.val (p.1, p.2) +
                off (trace width ask off p.1 p.2 d) j.val)] = h'
          rw [htrp]
          dsimp only [h']
          congr 2
          congr 1
          funext j
          have hq : qAff p = qAff p0 := by
            have h1 : qAff p -ᵥ qAff p0 ∈ (⊥ : Submodule K (Fin (width d) → K)) := hp.2
            exact vsub_eq_zero_iff_eq.1 ((Submodule.mem_bot K).1 h1)
          exact congrFun hq j
        obtain ⟨N', label', D', E', h1, h2, h3, h4, h5, h6⟩ :=
          ih (d + 1) (by omega) h' (Qslice p0) hlen' hprev' ⟨p0, hQslice_mem p0 hp0⟩ htr'
        rw [hQslice_dir p0 hp0] at h2
        exact ⟨N', label', D', E', h1, h2, h3, h4, h5, h6⟩
      choose Nsub Lsub Dsub Esub hSub using hsub_ih
      let Bsub : (X × U) → AffineSubspace K (X × U) := fun p0 =>
        if hp0 : p0 ∈ Q then
          let Ns := Nsub ⟨p0, hp0⟩
          let Ls := Lsub ⟨p0, hp0⟩
          let leaves := Ns.filter (fun p =>
            Ns.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1) = ∅)
          (leaves.inf (fun p => bad (Ls p))).comap (LinearMap.fst K X U).toAffineMap
        else ⊤
      let ψ : (X × U) →ᵃ[K] ((Fin (width d) → K) ⧸ RU) :=
        RU.mkQ.toAffineMap.comp qAff
      have hψ_rank : Module.finrank K (Q.map ψ).direction ≤ s := by
        have hdir : (Q.map ψ).direction = Rtot.map RU.mkQ := by
          rw [AffineSubspace.map_direction]
          change V.map (RU.mkQ.comp L) = (V.map L).map RU.mkQ
          rw [Submodule.map_comp]
        rw [hdir]
        have h1 := LinearMap.finrank_range_add_finrank_ker (RU.mkQ.domRestrict Rtot)
        have hr : LinearMap.range (RU.mkQ.domRestrict Rtot) = Rtot.map RU.mkQ := by
          ext z
          simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists,
            Submodule.mem_map]
          exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
        have hk : Module.finrank K (LinearMap.ker (RU.mkQ.domRestrict Rtot)) = Module.finrank K RU := by
          have hr2 : LinearMap.range (Rtot.subtype.domRestrict (LinearMap.ker (RU.mkQ.domRestrict Rtot))) = RU := by
            ext z
            simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.coe_subtype,
              Subtype.exists, LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact ⟨fun ⟨z', hzR, hzK, hzz⟩ => hzz ▸ hzK, fun hz => ⟨z, hRU_le hz, hz, rfl⟩⟩
          have hinj : Function.Injective (Rtot.subtype.domRestrict (LinearMap.ker (RU.mkQ.domRestrict Rtot))) :=
            fun a b hab => Subtype.ext (Subtype.ext hab)
          exact (LinearEquiv.ofInjective _ hinj).finrank_eq.trans (by rw [hr2])
        rw [hr, hk] at h1
        omega
      have hmiss : ∀ p0 ∈ Q, ∀ p1 ∈ Q, p1 ∈ Bsub p0 → ψ p1 ≠ ψ p0 := by
        intro p0 hp0 p1 hp1 hp1B hψeq
        have hdiff : qAff p0 - qAff p1 ∈ RU := by
          have : RU.mkQ (qAff p0 - qAff p1) = 0 := by
            rw [map_sub]
            exact sub_eq_zero.2 hψeq.symm
          exact (Submodule.Quotient.mk_eq_zero RU).1 this
        obtain ⟨w, hwD0, hwL⟩ := hdiff
        have hp1w : (p1.1, p1.2 + w) ∈ Qslice p0 := by
          refine ⟨?_, ?_⟩
          · have : (p1.1, p1.2 + w) = ((0 : X), w) +ᵥ p1 :=
              Prod.ext (by simp [vadd_eq_add]) (by simp [vadd_eq_add, add_comm])
            rw [this]
            exact AffineSubspace.vadd_mem_of_mem_direction hwD0 hp1
          · show qAff (p1.1, p1.2 + w) -ᵥ qAff p0 ∈ (⊥ : Submodule K (Fin (width d) → K))
            rw [Submodule.mem_bot, vsub_eq_zero_iff_eq]
            have : (p1.1, p1.2 + w) = ((0 : X), w) +ᵥ p1 :=
              Prod.ext (by simp [vadd_eq_add]) (by simp [vadd_eq_add, add_comm])
            rw [this, qAff.map_vadd]
            change L ((0 : X), w) + qAff p1 = qAff p0
            have : L ((0 : X), w) = LU w := rfl
            rw [this, hwL, sub_add_cancel]
        obtain ⟨l, hlN, hlLeaf, hlNotBad⟩ := (hSub ⟨p0, hp0⟩).2.2.2.2.2 p1.1 ⟨p1.2 + w, hp1w⟩
        simp only [Bsub, dif_pos hp0, AffineSubspace.mem_comap] at hp1B
        change p1.1 ∈ _ at hp1B
        have hmem_leaf : l ∈ (Nsub ⟨p0, hp0⟩).filter (fun p =>
            (Nsub ⟨p0, hp0⟩).filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1) = ∅) :=
          mem_filter.2 ⟨hlN, hlLeaf⟩
        have hle := Finset.inf_le (f := fun p => bad (Lsub ⟨p0, hp0⟩ p)) hmem_leaf
        exact hlNotBad (hle hp1B)
      obtain ⟨nc, pts, hnc1, hncs, hptsQ, hcov⟩ := greedy_prune Q hQne ψ Bsub hmiss s hψ_rank
      let idxSub : Fin nc → {p0 : X × U // p0 ∈ Q} := fun i => ⟨pts i, hptsQ i⟩
      let N : Finset (List ℕ) :=
        insert [] (Finset.univ.biUnion fun i : Fin nc => (Nsub (idxSub i)).image (fun p => i.val :: p))
      let label : List ℕ → Fin m := fun p =>
        match p with
        | [] => Lsub (idxSub ⟨0, by omega⟩) []
        | a :: rest =>
          if ha : a < nc then Lsub (idxSub ⟨a, ha⟩) rest
          else Lsub (idxSub ⟨0, by omega⟩) []
      let D : List ℕ → Submodule K U := fun p =>
        match p with
        | [] => D0
        | a :: rest =>
          if ha : a < nc then Dsub (idxSub ⟨a, ha⟩) rest
          else D0
      let E : List ℕ → Submodule K U := fun p =>
        match p with
        | [] => E0
        | a :: rest =>
          if ha : a < nc then Esub (idxSub ⟨a, ha⟩) rest
          else E0
      let ch : List ℕ → Finset (List ℕ) := fun p =>
        N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1)
      have hmemN_cons : ∀ (a : ℕ) (rest : List ℕ),
          (a :: rest) ∈ N ↔ ∃ ha : a < nc, rest ∈ Nsub (idxSub ⟨a, ha⟩) := by
        intro a rest
        simp only [N, mem_insert, List.cons_ne_nil, false_or, mem_biUnion, mem_univ, true_and,
          mem_image]
        constructor
        · rintro ⟨i, p, hp, heq⟩
          injection heq with ha hpr
          subst ha; subst hpr
          exact ⟨i.isLt, hp⟩
        · rintro ⟨ha, hrest⟩
          exact ⟨⟨a, ha⟩, rest, hrest, rfl⟩
      have hch_nil : ch [] = Finset.univ.image (fun i : Fin nc => [i.val]) := by
        ext q
        simp only [ch, mem_filter, List.nil_prefix, true_and, List.length_nil, zero_add,
          mem_image, mem_univ]
        cases q with
        | nil => simp
        | cons a rest =>
          simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff, hmemN_cons]
          constructor
          · rintro ⟨⟨ha, _⟩, rfl⟩
            exact ⟨⟨a, ha⟩, rfl⟩
          · rintro ⟨i, heq⟩
            injection heq with ha hrest
            subst ha; subst hrest
            exact ⟨⟨i.isLt, (hSub (idxSub i)).1⟩, rfl⟩
      have hch_cons : ∀ (a : ℕ) (ha : a < nc) (rest : List ℕ),
          ch (a :: rest) = ((Nsub (idxSub ⟨a, ha⟩)).filter (fun q =>
            List.IsPrefix rest q ∧ q.length = rest.length + 1)).image (fun q => a :: q) := by
        intro a ha rest
        ext q
        simp only [ch, mem_filter, mem_image]
        cases q with
        | nil => simp
        | cons b q' =>
          simp only [hmemN_cons, List.cons_prefix_cons, List.length_cons, add_left_inj]
          constructor
          · rintro ⟨⟨hb, hq'⟩, ⟨rfl, hpre⟩, hlenq⟩
            exact ⟨q', ⟨hq', hpre, hlenq⟩, rfl⟩
          · rintro ⟨q0, ⟨hq0, hpre, hlenq⟩, heq⟩
            injection heq with hb hqeq
            subst hb; subst hqeq
            exact ⟨⟨ha, hq0⟩, ⟨rfl, hpre⟩, hlenq⟩
      refine ⟨N, label, D, E, mem_insert_self _ _, rfl, ?_, ?_, ?_, ?_⟩
      · intro p hp
        cases p with
        | nil =>
          refine ⟨Nat.zero_le _, fun j hj => ?_⟩
          have hj0 : j = 0 := by simp at hj; omega
          subst hj0
          exact mem_insert_self _ _
        | cons a rest =>
          obtain ⟨ha, hrest⟩ := (hmemN_cons a rest).1 hp
          have ⟨hlenr, htake⟩ := (hSub (idxSub ⟨a, ha⟩)).2.2.1 rest hrest
          refine ⟨by simp; omega, fun j hj => ?_⟩
          cases j with
          | zero => exact mem_insert_self _ _
          | succ j =>
            rw [List.take_succ_cons, hmemN_cons]
            exact ⟨ha, htake j (by simp at hj; omega)⟩
      · intro p hp hne
        cases p with
        | nil =>
          have hcard : (ch []).card = nc := by
            rw [hch_nil, card_image_of_injective _ (fun i1 i2 h => Fin.ext (by injection h)),
              card_univ, Fintype.card_fin]
          refine ⟨inf_le_left, ?_, ?_⟩
          · change (ch []).card - 1 + (Module.finrank K D0 - Module.finrank K E0) ≤ width (d + 0)
            rw [hcard, add_zero]
            omega
          · intro q hq
            change q ∈ ch [] at hq
            rw [hch_nil, mem_image] at hq
            obtain ⟨i, _, rfl⟩ := hq
            simp only [D, E, dif_pos i.isLt]
            exact (hSub (idxSub i)).2.1
        | cons a rest =>
          obtain ⟨ha, hrest⟩ := (hmemN_cons a rest).1 hp
          have hne' : ((Nsub (idxSub ⟨a, ha⟩)).filter (fun q =>
              List.IsPrefix rest q ∧ q.length = rest.length + 1)).Nonempty := by
            change (ch (a :: rest)).Nonempty at hne
            rw [hch_cons a ha rest] at hne
            exact Finset.image_nonempty.1 hne
          have ⟨hED, hwid, hDq⟩ := (hSub (idxSub ⟨a, ha⟩)).2.2.2.1 rest hrest hne'
          refine ⟨by simpa only [D, E, dif_pos ha] using hED, ?_, ?_⟩
          · have hcard : (ch (a :: rest)).card =
                ((Nsub (idxSub ⟨a, ha⟩)).filter (fun q =>
                  List.IsPrefix rest q ∧ q.length = rest.length + 1)).card := by
              rw [hch_cons a ha rest, card_image_of_injective _ (fun _ _ h => by injection h)]
            have hD_eq : Module.finrank K ↥(D (a :: rest)) =
                Module.finrank K ↥(Dsub (idxSub ⟨a, ha⟩) rest) :=
              congrArg (fun S : Submodule K U => Module.finrank K ↥S) (by simp only [D, dif_pos ha])
            have hE_eq : Module.finrank K ↥(E (a :: rest)) =
                Module.finrank K ↥(Esub (idxSub ⟨a, ha⟩) rest) :=
              congrArg (fun S : Submodule K U => Module.finrank K ↥S) (by simp only [E, dif_pos ha])
            change (ch (a :: rest)).card - 1 +
              (Module.finrank K ↥(D (a :: rest)) - Module.finrank K ↥(E (a :: rest))) ≤
              width (d + (rest.length + 1))
            rw [hcard, show d + (rest.length + 1) = d + 1 + rest.length by omega, hD_eq, hE_eq]
            exact hwid
          · intro q hq
            change q ∈ ch (a :: rest) at hq
            rw [hch_cons a ha rest, mem_image] at hq
            obtain ⟨q0, hq0, rfl⟩ := hq
            simp only [D, E, dif_pos ha]
            exact hDq q0 hq0
      · intro p hp hemp
        cases p with
        | nil =>
          have hne : (ch []).Nonempty := by
            rw [hch_nil]; exact ⟨[0], mem_image.2 ⟨⟨0, by omega⟩, mem_univ _, rfl⟩⟩
          exact absurd hemp hne.ne_empty
        | cons a rest =>
          obtain ⟨ha, hrest⟩ := (hmemN_cons a rest).1 hp
          have hemp' : (Nsub (idxSub ⟨a, ha⟩)).filter (fun q =>
              List.IsPrefix rest q ∧ q.length = rest.length + 1) = ∅ := by
            change ch (a :: rest) = ∅ at hemp
            have := hch_cons a ha rest
            rw [hemp] at this
            exact Finset.image_eq_empty.1 this.symm
          have ⟨hdue, hker⟩ := (hSub (idxSub ⟨a, ha⟩)).2.2.2.2.1 rest hrest hemp'
          simp only [label, D, dif_pos ha, List.length_cons]
          exact ⟨by omega, hker⟩
      · intro x ⟨u, hxu⟩
        obtain ⟨i, hi⟩ := hcov (x, u) hxu
        simp only [Bsub, dif_pos (hptsQ i), AffineSubspace.mem_comap] at hi
        change x ∉ _ at hi
        have hex : ∃ l ∈ (Nsub (idxSub i)).filter (fun p =>
            (Nsub (idxSub i)).filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1) = ∅),
            x ∉ bad (Lsub (idxSub i) l) := by
          by_contra hall
          push_neg at hall
          apply hi
          have hmem_inf : ∀ (S : Finset (List ℕ)), (∀ l ∈ S, x ∈ bad (Lsub (idxSub i) l)) →
              x ∈ S.inf (fun p => bad (Lsub (idxSub i) p)) := by
            intro S
            induction S using Finset.induction with
            | empty => intro _; exact AffineSubspace.mem_top K X x
            | @insert a s _ ih =>
              intro h
              rw [Finset.inf_insert]
              exact ⟨h a (mem_insert_self a s), ih fun l hl => h l (mem_insert_of_mem hl)⟩
          exact hmem_inf _ hall
        obtain ⟨l, hl, hnotB⟩ := hex
        obtain ⟨hlN, hlLeaf⟩ := mem_filter.1 hl
        refine ⟨i.val :: l, (hmemN_cons i.val l).2 ⟨i.isLt, hlN⟩, ?_, ?_⟩
        · change ch (i.val :: l) = ∅; rw [hch_cons i.val i.isLt l, hlLeaf]; simp
        · simpa only [label, dif_pos i.isLt] using hnotB

end Forward

section Backward

lemma tree_to_proto {K : Type} [Field K] {n k t m r : ℕ}
    (P : AffineSubspace K (Fin n → K)) (bad : Fin m → AffineSubspace K (Fin n → K))
    (M : Fin m → (Fin k → K) →ₗ[K] (Fin t → K)) (width : ℕ → ℕ) (due : Fin m → Fin (r + 1))
    (N : Finset (List ℕ)) (label : List ℕ → Fin m) (D E : List ℕ → Submodule K (Fin k → K))
    (hroot : [] ∈ N) (hD0 : D [] = ⊤)
    (hclosed : ∀ p ∈ N, p.length ≤ r ∧ ∀ j ≤ p.length, p.take j ∈ N)
    (hstep : ∀ p ∈ N, (N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1)).Nonempty →
      E p ≤ D p ∧
      ((N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1)).card - 1) +
        (Module.finrank K (D p) - Module.finrank K (E p)) ≤ width p.length ∧
      ∀ q ∈ N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1), D q = E p)
    (hleaf : ∀ p ∈ N, N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1) = ∅ →
      p.length ≤ (due (label p)).val ∧ D p ≤ LinearMap.ker (M (label p)))
    (hcov : ∀ x ∈ P, ∃ p ∈ N,
      N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1) = ∅ ∧
      x ∉ bad (label p)) :
    ∃ (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
      (off : List (List K) → ℕ → K)
      (out : List (List K) → Option (Fin m × (Fin t → K))),
      ∀ x ∈ P, ∀ u : Fin k → K,
        (∃ d ≤ r, (out (trace width ask off x u d)).isSome = true) ∧
        ∀ d ≤ r, ∀ i y, out (trace width ask off x u d) = some (i, y) →
          d ≤ (due i).val ∧ x ∉ bad i ∧ y = M i u := by
  classical
  let X := Fin n → K
  let U := Fin k → K
  let Y := Fin t → K
  let ch : List ℕ → Finset (List ℕ) := fun p =>
    N.filter (fun q => List.IsPrefix p q ∧ q.length = p.length + 1)
  let Leaves : Finset (List ℕ) := N.filter (fun p => ch p = ∅)
  have hdisj : ∀ x ∈ P, ∃ l ∈ Leaves, x ∉ bad (label l) := by
    intro x hx
    obtain ⟨p, hpN, hpL, hpNot⟩ := hcov x hx
    exact ⟨p, mem_filter.2 ⟨hpN, hpL⟩, hpNot⟩
  obtain ⟨fLeaf, hfBad, hfSum⟩ := affine_separation P Leaves (fun l => bad (label l)) hdisj
  let F : List ℕ → X →ᵃ[K] K := fun p =>
    ∑ l ∈ Leaves.filter (fun l => List.IsPrefix p l), fLeaf l
  have hF_root : ∀ x ∈ P, F [] x = 1 := by
    intro x hx
    have hflt : Leaves.filter (fun l => List.IsPrefix [] l) = Leaves := by
      ext l; simp
    change (∑ l ∈ Leaves.filter (fun l => List.IsPrefix [] l), fLeaf l) x = 1
    rw [hflt]
    have heval : (∑ l ∈ Leaves, fLeaf l) x = ∑ l ∈ Leaves, fLeaf l x := by
      induction Leaves using Finset.induction with
      | empty => simp
      | @insert a s ha ih => simp [sum_insert ha, ih]
    rw [heval]
    exact hfSum x hx
  have hF_leaf : ∀ p ∈ Leaves, F p = fLeaf p := by
    intro p hp
    have hflt : Leaves.filter (fun l => List.IsPrefix p l) = {p} := by
      ext l
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hlL, hpre⟩
        by_contra hne
        have hlt : p.length < l.length := by
          have hle := hpre.length_le
          rcases eq_or_lt_of_le hle with heq | hlt
          · exact absurd (List.IsPrefix.eq_of_length hpre heq).symm hne
          · exact hlt
        have hqN : l.take (p.length + 1) ∈ N := (hclosed l (mem_filter.1 hlL).1).2 _ (by omega)
        have hqCh : l.take (p.length + 1) ∈ ch p := by
          refine mem_filter.2 ⟨hqN, ?_, by simp [List.length_take]; omega⟩
          obtain ⟨s, rfl⟩ := hpre
          exact ⟨s.take 1, by rw [List.take_append]; simp⟩
        have hpCh := (mem_filter.1 hp).2
        rw [hpCh] at hqCh
        exact notMem_empty _ hqCh
      · rintro rfl; exact ⟨hp, List.prefix_refl _⟩
    dsimp only [F]
    rw [hflt, sum_singleton]
  have hF_split : ∀ p ∈ N, (ch p).Nonempty →
      ∀ x : X, F p x = ∑ q ∈ ch p, F q x := by
    intro p hp hne x
    have hbi : Leaves.filter (fun l => List.IsPrefix p l) =
        (ch p).biUnion (fun q => Leaves.filter (fun l => List.IsPrefix q l)) := by
      ext l
      simp only [mem_filter, mem_biUnion]
      constructor
      · rintro ⟨hlL, hpre⟩
        have hne_pl : p ≠ l := by
          rintro rfl
          exact hne.ne_empty (mem_filter.1 hlL).2
        have hlt : p.length < l.length := by
          rcases eq_or_lt_of_le hpre.length_le with heq | hlt
          · exact absurd (List.IsPrefix.eq_of_length hpre heq) hne_pl
          · exact hlt
        let q := l.take (p.length + 1)
        have hqN : q ∈ N := (hclosed l (mem_filter.1 hlL).1).2 _ (by omega)
        have hqCh : q ∈ ch p := by
          refine mem_filter.2 ⟨hqN, ?_, by simp [q, List.length_take]; omega⟩
          obtain ⟨s, rfl⟩ := hpre
          dsimp only [q]
          rw [List.take_append, List.take_of_length_le (by omega)]
          exact List.prefix_append _ _
        refine ⟨q, hqCh, hlL, List.take_prefix _ _⟩
      · rintro ⟨q, hqCh, hlL, hql⟩
        exact ⟨hlL, (mem_filter.1 hqCh).2.1.trans hql⟩
    have hdisj_ch : Set.PairwiseDisjoint (ch p : Set (List ℕ))
        (fun q => Leaves.filter (fun l => List.IsPrefix q l)) := by
      intro q1 hq1 q2 hq2 hne12
      dsimp only [Function.onFun]
      rw [disjoint_left]
      intro l hl1 hl2
      have h1 := (mem_filter.1 hl1).2
      have h2 := (mem_filter.1 hl2).2
      have hlen1 := (mem_filter.1 hq1).2.2
      have hlen2 := (mem_filter.1 hq2).2.2
      have he1 : l.take (p.length + 1) = q1 := by
        obtain ⟨s, rfl⟩ := h1; rw [← hlen1, List.take_left]
      have he2 : l.take (p.length + 1) = q2 := by
        obtain ⟨s, rfl⟩ := h2; rw [← hlen2, List.take_left]
      exact hne12 (he1.symm.trans he2)
    have heval : ∀ (S : Finset (List ℕ)), (∑ l ∈ S, fLeaf l) x = ∑ l ∈ S, fLeaf l x := by
      intro S
      induction S using Finset.induction with
      | empty => simp
      | @insert a s ha ih => simp [sum_insert ha, ih]
    dsimp only [F]
    rw [hbi, heval, sum_biUnion hdisj_ch]
    exact sum_congr rfl fun q _ => (heval _).symm
  have hmeas_ex : ∀ p : List ℕ,
      ∃ (Φ : U →ₗ[K] (Fin (Module.finrank K (D p) - Module.finrank K (E p)) → K))
        (σ : (Fin (Module.finrank K (D p) - Module.finrank K (E p)) → K) →ₗ[K] U),
        (p ∈ N → (ch p).Nonempty →
          (∀ w, σ w ∈ D p) ∧ (∀ w, Φ (σ w) = w) ∧ (∀ u ∈ D p, Φ u = 0 ↔ u ∈ E p)) := by
    intro p
    by_cases hok : p ∈ N ∧ (ch p).Nonempty
    · obtain ⟨Φ, σ, h1, h2, h3⟩ := subspace_meas_map (hstep p hok.1 hok.2).1
      exact ⟨Φ, σ, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun hp hne => absurd ⟨hp, hne⟩ hok⟩
  choose Φ σ hΦσ using hmeas_ex
  let chList : List ℕ → List (List ℕ) := fun p => (ch p).toList
  let askNode : List ℕ → ℕ → (X × U) →ₗ[K] K := fun p j =>
    let s := (ch p).card - 1
    let d := Module.finrank K (D p) - Module.finrank K (E p)
    if h1 : j < s then
      if h2 : j < (chList p).length then
        (F ((chList p).get ⟨j, h2⟩)).linear.comp (LinearMap.fst K X U)
      else 0
    else if h3 : j - s < d then
      (LinearMap.proj ⟨j - s, h3⟩).comp ((Φ p).comp (LinearMap.snd K X U))
    else 0
  let offNode : List ℕ → ℕ → K := fun p j =>
    let s := (ch p).card - 1
    if h1 : j < s then
      if h2 : j < (chList p).length then
        F ((chList p).get ⟨j, h2⟩) 0
      else 0
    else 0
  let stepState : (List ℕ × K × U × Bool) → List K → (List ℕ × K × U × Bool) :=
    fun st ans =>
      let (p, v, uhat, done) := st
      if hok : done = false ∧ p ∈ N ∧ (ch p).Nonempty then
        let s := (ch p).card - 1
        let d := Module.finrank K (D p) - Module.finrank K (E p)
        let vals : Fin (chList p).length → K := fun idx =>
          if idx.val < s then ans.getD idx.val 0
          else v - ∑ j ∈ Finset.range s, ans.getD j 0
        let chosen : List ℕ :=
          if hex : ∃ idx : Fin (chList p).length, vals idx ≠ 0 then
            (chList p).get hex.choose
          else p
        let vNext : K :=
          if hex : ∃ idx : Fin (chList p).length, vals idx ≠ 0 then
            vals hex.choose
          else 0
        let yU : Fin d → K := fun j => ans.getD (s + j.val) 0
        let uNext : U := uhat + σ p (yU - Φ p uhat)
        (chosen, vNext, uNext, false)
      else (p, v, uhat, true)
  let evalHist : List (List K) → (List ℕ × K × U × Bool) := fun h =>
    h.foldl stepState ([], 1, 0, false)
  let ask : List (List K) → ℕ → (X × U) →ₗ[K] K := fun h j => askNode (evalHist h).1 j
  let off : List (List K) → ℕ → K := fun h j => offNode (evalHist h).1 j
  let out : List (List K) → Option (Fin m × Y) := fun h =>
    let (p, _, uhat, done) := evalHist h
    if done = false ∧ p ∈ N ∧ ch p = ∅ then some (label p, M (label p) uhat)
    else none
  refine ⟨ask, off, out, fun x hxP u => ?_⟩
  have hinv : ∀ d ≤ r,
      let st := evalHist (trace width ask off x u d)
      let p := st.1; let v := st.2.1; let uhat := st.2.2.1; let done := st.2.2.2
      (done = false → p ∈ N ∧ p.length = d ∧ v = F p x ∧ v ≠ 0 ∧ u - uhat ∈ D p) ∧
      (done = true → ∃ d0 < d, (out (trace width ask off x u d0)).isSome = true) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [trace, evalHist, List.foldl_nil, Bool.false_eq_true, IsEmpty.forall_iff, and_true]
      intro _
      refine ⟨hroot, rfl, (hF_root x hxP).symm, one_ne_zero, ?_⟩
      rw [hD0]; trivial
    | succ d ih =>
      intro hdr
      obtain ⟨ihF, ihT⟩ := ih (by omega)
      set h := trace width ask off x u d
      set st := evalHist h
      set p := st.1; set v := st.2.1; set uhat := st.2.2.1; set done := st.2.2.2
      set ans := List.ofFn (fun j : Fin (width d) => ask h j.val (x, u) + off h j.val)
      have heval_succ : evalHist (trace width ask off x u (d + 1)) = stepState st ans := by
        change (h ++ [ans]).foldl stepState ([], 1, 0, false) = stepState st ans
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [heval_succ]
      by_cases hdone : done = true
      · have hst : stepState st ans = (p, v, uhat, true) := by
          dsimp only [stepState]
          rw [dif_neg (by intro h1; exact Bool.noConfusion (h1.1.symm.trans hdone))]
        rw [hst]
        refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
        obtain ⟨d0, hd0, hsome⟩ := ihT hdone
        exact ⟨d0, by omega, hsome⟩
      · have hdoneF : done = false := Bool.eq_false_iff.2 hdone
        obtain ⟨hpN, hplen, hvF, hv0, huD⟩ := ihF hdoneF
        by_cases hch_ne : (ch p).Nonempty
        · have hok : done = false ∧ p ∈ N ∧ (ch p).Nonempty := ⟨hdoneF, hpN, hch_ne⟩
          have ⟨hED, hwid, hDq⟩ := hstep p hpN hch_ne
          have ⟨hσD, hΦσ_id, hΦker⟩ := hΦσ p hpN hch_ne
          set s := (ch p).card - 1
          set dd := Module.finrank K (D p) - Module.finrank K (E p)
          have hlen_ch : (chList p).length = (ch p).card := Finset.length_toList _
          have hcard_pos : 0 < (ch p).card := hch_ne.card_pos
          have hs_wid : s + dd ≤ width d := by rw [← hplen]; exact hwid
          have hans_get : ∀ j (hj : j < width d), ans.getD j 0 = askNode p j (x, u) + offNode p j := by
            intro j hj
            simp only [ans, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj,
              Option.getD_some, ask, off]
            rfl
          have hans_ch : ∀ (j : ℕ) (hj : j < s),
              ans.getD j 0 = F ((chList p).get ⟨j, by omega⟩) x := by
            intro j hj
            rw [hans_get j (by omega)]
            have hj1 : j < (ch p).card - 1 := hj
            have hj2 : j < (chList p).length := by omega
            dsimp only [askNode, offNode]
            simp only [hj1, hj2, ↓reduceDIte, ↓reduceIte, LinearMap.comp_apply, LinearMap.fst_apply]
            have haff := (F ((chList p).get ⟨j, hj2⟩)).map_vadd (0 : X) x
            simpa [vadd_eq_add] using haff.symm
          have hsum_ch : ∑ idx : Fin (chList p).length, F ((chList p).get idx) x = F p x := by
            rw [hF_split p hpN hch_ne x]
            have hnd : (chList p).Nodup := Finset.nodup_toList _
            have hset : ∀ q, q ∈ chList p ↔ q ∈ ch p := fun q => Finset.mem_toList
            have hmap_eq : List.ofFn (fun idx : Fin (chList p).length => F ((chList p).get idx) x) =
                (chList p).map (fun q => F q x) := by
              apply List.ext_getElem
              · simp
              · intro i h1 h2; simp
            calc ∑ idx : Fin (chList p).length, F ((chList p).get idx) x
                = (List.ofFn (fun idx : Fin (chList p).length => F ((chList p).get idx) x)).sum :=
                  (List.sum_ofFn).symm
              _ = ((chList p).map (fun q => F q x)).sum := by rw [hmap_eq]
              _ = ∑ q ∈ (chList p).toFinset, F q x := (List.sum_toFinset _ hnd).symm
              _ = ∑ q ∈ ch p, F q x := by
                  congr 1; ext q; simp [hset]
          have hvals_eq : ∀ idx : Fin (chList p).length,
              (if idx.val < s then ans.getD idx.val 0
               else v - ∑ j ∈ Finset.range s, ans.getD j 0) = F ((chList p).get idx) x := by
            intro idx
            by_cases hlt : idx.val < s
            · rw [if_pos hlt]; exact hans_ch idx.val hlt
            · rw [if_neg hlt]
              have hidx_eq : idx.val = s := by omega
              have hsum_pre : ∑ j ∈ Finset.range s, ans.getD j 0 =
                  ∑ i ∈ univ.filter (fun i : Fin (chList p).length => i.val < s),
                    F ((chList p).get i) x := by
                refine sum_bij (fun j hj => ⟨j, by rw [mem_range] at hj; omega⟩) ?_ ?_ ?_ ?_
                · intro j hj; exact mem_filter.2 ⟨mem_univ _, mem_range.1 hj⟩
                · intro j1 _ j2 _ heq; exact congrArg Fin.val heq
                · intro i hi; exact ⟨i.val, mem_range.2 (mem_filter.1 hi).2, Fin.ext rfl⟩
                · intro j hj; exact hans_ch j (mem_range.1 hj)
              have hsplit_fin : ∑ i : Fin (chList p).length, F ((chList p).get i) x =
                  (∑ i ∈ univ.filter (fun i : Fin (chList p).length => i.val < s),
                    F ((chList p).get i) x) + F ((chList p).get idx) x := by
                rw [← sum_filter_add_sum_filter_not univ (fun i : Fin (chList p).length => i.val < s)]
                congr 1
                have hsing : univ.filter (fun i : Fin (chList p).length => ¬ i.val < s) = {idx} := by
                  ext i
                  simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
                  omega
                rw [hsing, sum_singleton]
              rw [hsum_pre, hvF, ← hsum_ch, hsplit_fin, add_sub_cancel_left]
          have hex : ∃ idx : Fin (chList p).length,
              (if idx.val < s then ans.getD idx.val 0
               else v - ∑ j ∈ Finset.range s, ans.getD j 0) ≠ 0 := by
            by_contra hall
            push_neg at hall
            have h0 : F p x = 0 := by
              rw [← hsum_ch]
              exact sum_eq_zero fun idx _ => by rw [← hvals_eq idx]; exact hall idx
            exact hv0 (hvF.trans h0)
          have hst_eq : stepState st ans =
              ((chList p).get hex.choose,
               (if hex.choose.val < s then ans.getD hex.choose.val 0
                else v - ∑ j ∈ Finset.range s, ans.getD j 0),
               uhat + σ p ((fun j : Fin dd => ans.getD (s + j.val) 0) - Φ p uhat),
               false) := by
            dsimp only [stepState]
            rw [dif_pos hok, dif_pos hex, dif_pos hex]
          rw [hst_eq]
          refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
          have hqCh : (chList p).get hex.choose ∈ ch p :=
            Finset.mem_toList.1 (List.get_mem _ _)
          have hqN : (chList p).get hex.choose ∈ N := (mem_filter.1 hqCh).1
          have hqLen : ((chList p).get hex.choose).length = d + 1 := by
            rw [(mem_filter.1 hqCh).2.2, hplen]
          have hyU_eq : (fun j : Fin dd => ans.getD (s + j.val) 0) = Φ p u := by
            funext j
            rw [hans_get (s + j.val) (by omega)]
            have hnot1 : ¬ (s + j.val < (ch p).card - 1) := by omega
            have h3 : (s + j.val) - ((ch p).card - 1) <
                Module.finrank K (D p) - Module.finrank K (E p) := by omega
            dsimp only [askNode, offNode]
            simp only [hnot1, h3, ↓reduceDIte, ↓reduceIte, add_zero,
              LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.proj_apply]
            have hsub : (⟨(s + j.val) - ((ch p).card - 1), h3⟩ : Fin dd) = j :=
              Fin.ext (by dsimp only [s]; omega)
            rw [hsub]
          refine ⟨hqN, hqLen, hvals_eq hex.choose, hex.choose_spec, ?_⟩
          rw [hDq _ hqCh, hyU_eq]
          have hmemD : u - (uhat + σ p (Φ p u - Φ p uhat)) ∈ D p := by
            have : u - (uhat + σ p (Φ p u - Φ p uhat)) = (u - uhat) - σ p (Φ p u - Φ p uhat) := by abel
            rw [this]
            exact (D p).sub_mem huD (hσD _)
          refine (hΦker _ hmemD).1 ?_
          rw [map_sub, map_add, hΦσ_id]
          abel
        · have hch_emp : ch p = ∅ := not_nonempty_iff_eq_empty.1 hch_ne
          have hst : stepState st ans = (p, v, uhat, true) := by
            dsimp only [stepState]
            rw [dif_neg (by intro h1; exact hch_ne h1.2.2)]
          rw [hst]
          refine ⟨fun h => Bool.noConfusion h, fun _ => ⟨d, Nat.lt_succ_self d, ?_⟩⟩
          change (if st.2.2.2 = false ∧ st.1 ∈ N ∧ ch st.1 = ∅ then
            some (label st.1, M (label st.1) st.2.2.1) else none).isSome = true
          rw [if_pos ⟨hdoneF, hpN, hch_emp⟩]
          rfl
  constructor
  · obtain ⟨hF, hT⟩ := hinv r le_rfl
    set st := evalHist (trace width ask off x u r)
    cases hd : st.2.2.2
    · obtain ⟨hpN, hplen, _, _, _⟩ := hF hd
      have hch_emp : ch st.1 = ∅ := by
        by_contra hne
        obtain ⟨q, hq⟩ := nonempty_iff_ne_empty.2 hne
        have hqle := (hclosed q (mem_filter.1 hq).1).1
        have hqlen := (mem_filter.1 hq).2.2
        omega
      refine ⟨r, le_rfl, ?_⟩
      change (if st.2.2.2 = false ∧ st.1 ∈ N ∧ ch st.1 = ∅ then
        some (label st.1, M (label st.1) st.2.2.1) else none).isSome = true
      rw [if_pos ⟨hd, hpN, hch_emp⟩]
      rfl
    · obtain ⟨d0, hd0, hsome⟩ := hT hd
      exact ⟨d0, hd0.le, hsome⟩
  · intro d hdr i y hout
    obtain ⟨hF, _⟩ := hinv d hdr
    simp only [out] at hout
    split_ifs at hout with hcond
    injection hout with hpair
    injection hpair with hi hy
    obtain ⟨hpN, hplen, hvF, hv0, huD⟩ := hF hcond.1
    have ⟨hdue, hker⟩ := hleaf _ hpN hcond.2.2
    have hmemL : (evalHist (trace width ask off x u d)).1 ∈ Leaves :=
      mem_filter.2 ⟨hpN, hcond.2.2⟩
    have hdue' : d ≤ (due i).val := by
      calc d = (evalHist (trace width ask off x u d)).1.length := hplen.symm
        _ ≤ (due (label (evalHist (trace width ask off x u d)).1)).val := hdue
        _ = (due i).val := by rw [hi]
    refine ⟨hdue', ?_, ?_⟩
    · intro hxB
      rw [← hi] at hxB
      have h0 : F (evalHist (trace width ask off x u d)).1 x = 0 := by
        rw [hF_leaf _ hmemL]
        exact hfBad _ hmemL x hxB
      exact hv0 (hvF.trans h0)
    · rw [← hi, ← hy]
      have h0 : M (label (evalHist (trace width ask off x u d)).1)
          (u - (evalHist (trace width ask off x u d)).2.2.1) = 0 := hker huD
      rw [map_sub, sub_eq_zero] at h0
      exact h0.symm

end Backward

lemma main_426 : (∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n k t m r : ℕ),
    let X := Fin n → K
    let U := Fin k → K
    let Y := Fin t → K
    let H := List (List K)
    ∀ (P : AffineSubspace K X) (bad : Fin m → AffineSubspace K X)
      (M : Fin m → U →ₗ[K] Y) (width : ℕ → ℕ) (due : Fin m → Fin (r + 1)),
      (∃ x : X, x ∈ P) →
      ((∃ (ask : H → ℕ → (X × U) →ₗ[K] K) (off : H → ℕ → K)
          (out : H → Option (Fin m × Y)),
        ∀ x ∈ P, ∀ u : U,
          let path := (List.range r).foldl (fun (h : H) (s : ℕ) =>
            h ++ [List.ofFn (fun j : Fin (width s) => ask h j.val (x, u) + off h j.val)]) []
          (∃ d ≤ r, (out (path.take d)).isSome = true) ∧
          ∀ d ≤ r, ∀ i y, out (path.take d) = some (i, y) →
            d ≤ (due i).val ∧ x ∉ bad i ∧ y = M i u) ↔
      ∃ (N : Finset (List ℕ)) (label : List ℕ → Fin m) (D E : List ℕ → Submodule K U),
        let children := fun p : List ℕ => N.filter (fun q =>
          List.IsPrefix p q ∧ q.length = p.length + 1)
        [] ∈ N ∧ D [] = ⊤ ∧ (∀ p ∈ N, p.length ≤ r ∧ ∀ j ≤ p.length, p.take j ∈ N) ∧
        (∀ p ∈ N, (children p).Nonempty → E p ≤ D p ∧
          ((children p).card - 1) + (Module.finrank K (D p) - Module.finrank K (E p)) ≤ width p.length ∧
          ∀ q ∈ children p, D q = E p) ∧
        (∀ p ∈ N, children p = ∅ →
          p.length ≤ (due (label p)).val ∧ D p ≤ LinearMap.ker (M (label p))) ∧
        ∀ x ∈ P, ∃ p ∈ N, children p = ∅ ∧ x ∉ bad (label p))) := by
  intro K _ _ _ n k t m r X U Y H P bad M width due ⟨x0, hx0⟩
  constructor
  · rintro ⟨ask, off, out, hproto⟩
    have htr_proto : ∀ x ∈ P, ∀ u : U,
        (∃ d ≤ r, (out (trace width ask off x u d)).isSome = true) ∧
        ∀ d ≤ r, ∀ i y, out (trace width ask off x u d) = some (i, y) →
          d ≤ (due i).val ∧ x ∉ bad i ∧ y = M i u := by
      intro x hx u
      have hp := hproto x hx u
      dsimp only at hp
      have heq : ∀ d ≤ r, ((List.range r).foldl (fun (h : H) (s : ℕ) =>
          h ++ [List.ofFn (fun j : Fin (width s) => ask h j.val (x, u) + off h j.val)]) []).take d =
          trace width ask off x u d := fun d hd => by
        rw [foldl_range_eq_trace, trace_take width ask off x u hd]
      constructor
      · obtain ⟨d, hd, hsome⟩ := hp.1
        exact ⟨d, hd, by rwa [← heq d hd]⟩
      · intro d hd i y hout
        exact hp.2 d hd i y (by rwa [heq d hd])
    let Q0 : AffineSubspace K (X × U) := P.comap (LinearMap.fst K X U).toAffineMap
    have hQ0ne : (Q0 : Set (X × U)).Nonempty := ⟨(x0, 0), hx0⟩
    have hQ0dir : Q0.direction.comap (LinearMap.inr K X U) = ⊤ := by
      ext w
      simp only [Submodule.mem_comap, LinearMap.inr_apply, Submodule.mem_top, iff_true]
      have h1 : (x0, w) ∈ Q0 := hx0
      have h2 : (x0, (0 : U)) ∈ Q0 := hx0
      have hsub := AffineSubspace.vsub_mem_direction h1 h2
      simpa [vsub_eq_sub] using hsub
    obtain ⟨N, label, D, E, h1, h2, h3, h4, h5, h6⟩ :=
      proto_to_tree P bad M width due ask off out htr_proto r 0 (zero_add r) [] Q0
        rfl (fun _ hj => absurd hj (Nat.not_lt_zero _)) hQ0ne (fun p hp => ⟨hp, rfl⟩)
    rw [hQ0dir] at h2
    refine ⟨N, label, D, E, h1, h2, h3, ?_, ?_, ?_⟩
    · intro p hp hne
      have := h4 p hp hne
      simpa only [zero_add] using this
    · intro p hp hemp
      have := h5 p hp hemp
      simpa only [zero_add] using this
    · intro x hx
      exact h6 x ⟨0, hx⟩
  · rintro ⟨N, label, D, E, hroot, hD0, hclosed, hstep, hleaf, hcov⟩
    obtain ⟨ask, off, out, hproto⟩ :=
      tree_to_proto P bad M width due N label D E hroot hD0 hclosed hstep hleaf hcov
    refine ⟨ask, off, out, fun x hx u => ?_⟩
    dsimp only
    have heq : ∀ d ≤ r, ((List.range r).foldl (fun (h : H) (s : ℕ) =>
        h ++ [List.ofFn (fun j : Fin (width s) => ask h j.val (x, u) + off h j.val)]) []).take d =
        trace width ask off x u d := fun d hd => by
      rw [foldl_range_eq_trace, trace_take width ask off x u hd]
    obtain ⟨h1, h2⟩ := hproto x hx u
    constructor
    · obtain ⟨d, hd, hsome⟩ := h1
      exact ⟨d, hd, by rwa [heq d hd]⟩
    · intro d hd i y hout
      rw [heq d hd] at hout
      exact h2 d hd i y hout

end PEqualNP.Outside.L_pcx_426_aux

theorem PEqualNP.Outside.L_pcx_426 : (∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n k t m r : ℕ),
  let X := Fin n → K
  let U := Fin k → K
  let Y := Fin t → K
  let H := List (List K)
  ∀ (P : AffineSubspace K X) (bad : Fin m → AffineSubspace K X)
    (M : Fin m → U →ₗ[K] Y) (width : ℕ → ℕ) (due : Fin m → Fin (r+1)),
    (∃ x : X, x ∈ P) →
    ((∃ (ask : H → ℕ → (X × U) →ₗ[K] K) (off : H → ℕ → K)
        (out : H → Option (Fin m × Y)),
      ∀ x ∈ P, ∀ u : U,
        let path := (List.range r).foldl (fun (h : H) (s : ℕ) =>
          h ++ [List.ofFn (fun j : Fin (width s) => ask h j.val (x,u) + off h j.val)]) []
        (∃ d ≤ r, (out (path.take d)).isSome = true) ∧
        ∀ d ≤ r, ∀ i y, out (path.take d) = some (i,y) →
          d ≤ (due i).val ∧ x ∉ bad i ∧ y = M i u) ↔
    ∃ (N : Finset (List ℕ)) (label : List ℕ → Fin m) (D E : List ℕ → Submodule K U),
      let children := fun p : List ℕ => N.filter (fun q =>
        List.IsPrefix p q ∧ q.length = p.length+1)
      [] ∈ N ∧ D [] = ⊤ ∧ (∀ p ∈ N, p.length ≤ r ∧ ∀ j ≤ p.length, p.take j ∈ N) ∧
      (∀ p ∈ N, (children p).Nonempty → E p ≤ D p ∧
        ((children p).card - 1) + (Module.finrank K (D p) - Module.finrank K (E p)) ≤ width p.length ∧
        ∀ q ∈ children p, D q = E p) ∧
      (∀ p ∈ N, children p = ∅ →
        p.length ≤ (due (label p)).val ∧ D p ≤ LinearMap.ker (M (label p))) ∧
      ∀ x ∈ P, ∃ p ∈ N, children p = ∅ ∧ x ∉ bad (label p))) :=
  PEqualNP.Outside.L_pcx_426_aux.main_426
