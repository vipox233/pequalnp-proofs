import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_425_aux

def traceAux {K : Type*} (len : List (List K) → ℕ)
    (value : List (List K) → ℕ → K) : ℕ → List (List K)
  | 0 => []
  | d + 1 =>
    let h := traceAux len value d
    h ++ [List.ofFn (fun j : Fin (len h) => value h j.val)]

lemma traceAux_length {K : Type*} (len : List (List K) → ℕ)
    (value : List (List K) → ℕ → K) (d : ℕ) :
    (traceAux len value d).length = d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp [traceAux, ih]

lemma foldl_range_eq_traceAux {K : Type*} (len : List (List K) → ℕ)
    (value : List (List K) → ℕ → K) (r : ℕ) :
    (List.range r).foldl (fun (h : List (List K)) (_ : ℕ) =>
      h ++ [List.ofFn (fun j : Fin (len h) => value h j.val)]) [] =
    traceAux len value r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

lemma traceAux_take {K : Type*} (len : List (List K) → ℕ)
    (value : List (List K) → ℕ → K) {d r : ℕ} (hdr : d ≤ r) :
    (traceAux len value r).take d = traceAux len value d := by
  induction r with
  | zero =>
    have hd : d = 0 := Nat.le_zero.mp hdr
    subst hd; rfl
  | succ r ih =>
    by_cases h : d = r + 1
    · subst h
      rw [List.take_of_length_le (by rw [traceAux_length])]
    · have hdr' : d ≤ r := by omega
      simp only [traceAux]
      rw [List.take_append_of_le_length (by rw [traceAux_length]; exact hdr')]
      exact ih hdr'

lemma proj_add_symm {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {P Q : Submodule K V} (hPQ : IsCompl P Q) (x : V) :
    (Submodule.projectionOnto P Q hPQ x).1 + (Submodule.projectionOnto Q P hPQ.symm x).1 = x := by
  have hx : x ∈ P ⊔ Q := by rw [hPQ.sup_eq_top]; trivial
  rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
  rw [map_add, map_add,
    Submodule.projectionOnto_apply_left hPQ ⟨a, ha⟩,
    Submodule.projectionOnto_apply_right hPQ ⟨b, hb⟩,
    Submodule.projectionOnto_apply_right hPQ.symm ⟨a, ha⟩,
    Submodule.projectionOnto_apply_left hPQ.symm ⟨b, hb⟩]
  simp

lemma exists_linear_section {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (f : U →ₗ[K] W) (D : Submodule K U) :
    ∃ sec : (D.map f : Submodule K W) →ₗ[K] D,
      ∀ y : D.map f, f (sec y).1 = y.1 := by
  let g : D →ₗ[K] D.map f :=
    { toFun := fun u => ⟨f u.1, ⟨u.1, u.2, rfl⟩⟩
      map_add' := fun x y => by apply Subtype.ext; exact map_add f x.1 y.1
      map_smul' := fun c x => by apply Subtype.ext; exact map_smul f c x.1 }
  have hg_surj : Function.Surjective g := by
    rintro ⟨y, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.ker g)
  let gQ : Q →ₗ[K] D.map f := g.comp Q.subtype
  have hgQ_inj : Function.Injective gQ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    apply Subtype.ext
    have hmem : q.1 ∈ LinearMap.ker g ⊓ Q := ⟨hq, q.2⟩
    rw [hQ.inf_eq_bot] at hmem
    exact hmem
  have hgQ_surj : Function.Surjective gQ := by
    intro y
    rcases hg_surj y with ⟨u, rfl⟩
    let pQ : D →ₗ[K] Q := Submodule.projectionOnto Q (LinearMap.ker g) hQ.symm
    let pK : D →ₗ[K] LinearMap.ker g := Submodule.projectionOnto (LinearMap.ker g) Q hQ
    refine ⟨pQ u, ?_⟩
    have hsum : (pK u).1 + (pQ u).1 = u := by
      have := proj_add_symm hQ u
      simpa [pK, pQ] using this
    have hgk : g (pK u).1 = 0 := (pK u).2
    calc gQ (pQ u) = g (pQ u).1 := rfl
      _ = g (pK u).1 + g (pQ u).1 := by rw [hgk, zero_add]
      _ = g ((pK u).1 + (pQ u).1) := (map_add g _ _).symm
      _ = g u := by rw [hsum]
  let e : Q ≃ₗ[K] D.map f := LinearEquiv.ofBijective gQ ⟨hgQ_inj, hgQ_surj⟩
  refine ⟨Q.subtype.comp e.symm.toLinearMap, fun y => ?_⟩
  have h1 : gQ (e.symm y) = y := e.apply_symm_apply y
  exact congrArg Subtype.val h1

lemma exists_drop_forms {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (D E : Submodule K U) (hED : E ≤ D) :
    ∃ φ : U →ₗ[K] (Fin (Module.finrank K D - Module.finrank K E) → K),
      ∀ u ∈ D, φ u = 0 ↔ u ∈ E := by
  let E' : Submodule K D := E.comap D.subtype
  have hE'_fin : Module.finrank K E' = Module.finrank K E := by
    let e : E' ≃ₗ[K] E :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨⟨y.1, hED y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl E'
  have hQ'_fin : Module.finrank K Q' = Module.finrank K D - Module.finrank K E := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq E' Q'
    rw [hQ'.sup_eq_top, hQ'.inf_eq_bot, finrank_top, finrank_bot, add_zero, hE'_fin] at h1
    omega
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl D
  let pD : U →ₗ[K] D := Submodule.projectionOnto D R hR
  let pQ' : D →ₗ[K] Q' := Submodule.projectionOnto Q' E' hQ'.symm
  let bQ' : Module.Basis (Fin (Module.finrank K D - Module.finrank K E)) K Q' :=
    Module.finBasisOfFinrankEq K Q' hQ'_fin
  refine ⟨bQ'.equivFun.toLinearMap.comp (pQ'.comp pD), fun u hu => ?_⟩
  have hpD : pD u = ⟨u, hu⟩ := Submodule.projectionOnto_apply_left hR ⟨u, hu⟩
  simp only [LinearMap.comp_apply, hpD, LinearEquiv.coe_toLinearMap]
  constructor
  · intro h0
    have hpQ0 : pQ' ⟨u, hu⟩ = 0 := bQ'.equivFun.injective (by simpa using h0)
    have hsum := proj_add_symm hQ' ⟨u, hu⟩
    have hmem : (Submodule.projectionOnto E' Q' hQ' ⟨u, hu⟩).1 = ⟨u, hu⟩ := by
      have : (pQ' ⟨u, hu⟩).1 = 0 := congrArg Subtype.val hpQ0
      simpa [pQ', this] using hsum
    have hE'mem : (⟨u, hu⟩ : D) ∈ E' := hmem ▸ (Submodule.projectionOnto E' Q' hQ' ⟨u, hu⟩).2
    exact hE'mem
  · intro huE
    have hpQ0 : pQ' ⟨u, hu⟩ = 0 := Submodule.projectionOnto_apply_right hQ'.symm ⟨⟨u, hu⟩, huE⟩
    simp [hpQ0]

lemma finrank_map_add_inf_ker {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U] (f : U →ₗ[K] W) (D : Submodule K U) :
    Module.finrank K (D.map f) + Module.finrank K (D ⊓ LinearMap.ker f : Submodule K U) =
      Module.finrank K D := by
  let g : D →ₗ[K] W := f.comp D.subtype
  have hfn := LinearMap.finrank_range_add_finrank_ker g
  have hrange : LinearMap.range g = D.map f := by
    ext w
    simp [g, LinearMap.mem_range, Submodule.mem_map]
  have hker : Module.finrank K (LinearMap.ker g) = Module.finrank K (D ⊓ LinearMap.ker f : Submodule K U) := by
    let e : LinearMap.ker g ≃ₗ[K] (D ⊓ LinearMap.ker f : Submodule K U) :=
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  rw [hrange, hker] at hfn
  exact hfn

structure SimState (K : Type) [Field K] (n k : ℕ) where
  sim : List (List K)
  D : Submodule K (Fin k → K)
  fL : (Fin n → K) →ₗ[K] (Fin k → K)
  fC : Fin k → K

noncomputable def buildStep {K : Type} [Field K] {n k : ℕ}
    (width : ℕ → ℕ)
    (ask : List (List K) → ℕ → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (off : List (List K) → ℕ → K)
    (st : SimState K n k) :
    Σ' (len : ℕ)
       (E : Submodule K (Fin k → K))
       (askX : ℕ → (Fin n → K) →ₗ[K] K)
       (offX : ℕ → K)
       (next : List K → SimState K n k),
      E ≤ st.D ∧
      len + (Module.finrank K st.D - Module.finrank K E) ≤ width st.sim.length ∧
      (∀ z : List K, (next z).D = E ∧ (next z).sim.length = st.sim.length + 1 ∧ List.IsPrefix st.sim (next z).sim) ∧
      (∀ (x : Fin n → K) (u : Fin k → K),
        let z := List.ofFn (fun j : Fin len => askX j.val x + offX j.val)
        u ∈ E →
        ((next z).fL x + (next z).fC + u - (st.fL x + st.fC)) ∈ st.D ∧
        (next z).sim = st.sim ++ [List.ofFn (fun j : Fin (width st.sim.length) =>
          ask st.sim j.val (x, (next z).fL x + (next z).fC + u) + off st.sim j.val)]) := by
  let w := width st.sim.length
  let T : (Fin k → K) →ₗ[K] (Fin w → K) :=
    { toFun := fun u j => ask st.sim j.val (0, u)
      map_add' := fun u1 u2 => by
        ext j
        have : ((0 : Fin n → K), u1 + u2) = (0, u1) + (0, u2) := by simp
        rw [this, map_add]; rfl
      map_smul' := fun c u => by
        ext j
        have : ((0 : Fin n → K), c • u) = c • (0, u) := by simp
        rw [this, map_smul]; rfl }
  let S : (Fin n → K) →ₗ[K] (Fin w → K) :=
    { toFun := fun x j => ask st.sim j.val (x, 0)
      map_add' := fun x1 x2 => by
        ext j
        have : (x1 + x2, (0 : Fin k → K)) = (x1, 0) + (x2, 0) := by simp
        rw [this, map_add]; rfl
      map_smul' := fun c x => by
        ext j
        have : (c • x, (0 : Fin k → K)) = c • (x, 0) := by simp
        rw [this, map_smul]; rfl }
  let cvec : Fin w → K := fun j => off st.sim j.val
  let TD : Submodule K (Fin w → K) := st.D.map T
  let E : Submodule K (Fin k → K) := st.D ⊓ LinearMap.ker T
  have hED : E ≤ st.D := inf_le_left
  let Q : Submodule K (Fin w → K) := Classical.choose (Submodule.exists_isCompl TD)
  have hQ : IsCompl TD Q := Classical.choose_spec (Submodule.exists_isCompl TD)
  let len : ℕ := Module.finrank K Q
  have hlen_bound : len + (Module.finrank K st.D - Module.finrank K E) ≤ w := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq TD Q
    rw [hQ.sup_eq_top, hQ.inf_eq_bot, finrank_top, finrank_bot, add_zero, Module.finrank_pi,
      Fintype.card_fin] at h1
    have h2 : Module.finrank K TD + Module.finrank K E = Module.finrank K st.D :=
      finrank_map_add_inf_ker T st.D
    omega
  let projQ : (Fin w → K) →ₗ[K] Q := Submodule.projectionOnto Q TD hQ.symm
  let projTD : (Fin w → K) →ₗ[K] TD := Submodule.projectionOnto TD Q hQ
  let bQ : Module.Basis (Fin len) K Q := Module.finBasisOfFinrankEq K Q rfl
  let coordQ : (Fin w → K) →ₗ[K] (Fin len → K) := bQ.equivFun.toLinearMap.comp projQ
  let sec : TD →ₗ[K] st.D := Classical.choose (exists_linear_section T st.D)
  have hsec : ∀ y : TD, T (sec y).1 = y.1 := Classical.choose_spec (exists_linear_section T st.D)
  let linComb : (Fin n → K) →ₗ[K] (Fin w → K) := S + T.comp st.fL
  let constComb : Fin w → K := T st.fC + cvec
  let askX : ℕ → (Fin n → K) →ₗ[K] K := fun j =>
    if hj : j < len then (LinearMap.proj ⟨j, hj⟩).comp (coordQ.comp linComb) else 0
  let offX : ℕ → K := fun j =>
    if hj : j < len then coordQ constComb ⟨j, hj⟩ else 0
  let qzOf : List K → Q := fun z => bQ.equivFun.symm (fun j : Fin len => z.getD j.val 0)
  let ΔL : (Fin n → K) →ₗ[K] (Fin k → K) := st.D.subtype.comp (sec.comp (projTD.comp linComb))
  let next : List K → SimState K n k := fun z =>
    let qz := qzOf z
    let ΔC : Fin k → K := (sec (projTD (constComb - qz.1))).1
    { sim := st.sim ++ [List.ofFn (fun j : Fin w => qz.1 j)]
      D := E
      fL := st.fL - ΔL
      fC := st.fC - ΔC }
  refine ⟨len, E, askX, offX, next, hED, hlen_bound, fun z => ⟨rfl, by simp [next], List.prefix_append _ _⟩, ?_⟩
  intro x u z huE
  have hqz : (qzOf z : Q) = projQ (linComb x + constComb) := by
    have hfun : (fun j : Fin len => z.getD j.val 0) = coordQ (linComb x + constComb) := by
      ext j
      simp only [z, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, ↓reduceDIte,
        Option.getD_some, askX, offX, LinearMap.comp_apply, LinearMap.proj_apply, map_add,
        Pi.add_apply]
    dsimp only [qzOf]
    rw [hfun]
    exact bQ.equivFun.symm_apply_apply (projQ (linComb x + constComb))
  have hmemD : (next z).fL x + (next z).fC + u - (st.fL x + st.fC) ∈ st.D := by
    have h1 : (next z).fL x + (next z).fC + u - (st.fL x + st.fC) =
        -(ΔL x) - (sec (projTD (constComb - (qzOf z).1))).1 + u := by
      simp only [next, LinearMap.sub_apply]
      abel
    rw [h1]
    exact st.D.add_mem (st.D.sub_mem (st.D.neg_mem (sec (projTD (linComb x))).2)
      (sec (projTD (constComb - (qzOf z).1))).2) (hED huE)
  refine ⟨hmemD, ?_⟩
  simp only [next]
  congr 2
  congr 1
  funext j
  have hsplit : ask st.sim j.val (x, (st.fL - ΔL) x + (st.fC - (sec (projTD (constComb - (qzOf z).1))).1) + u) +
      off st.sim j.val =
      (linComb x + constComb - T (ΔL x) - T (sec (projTD (constComb - (qzOf z).1))).1 + T u) j := by
    have hpair : (x, (st.fL - ΔL) x + (st.fC - (sec (projTD (constComb - (qzOf z).1))).1) + u) =
        (x, 0) + (0, (st.fL - ΔL) x + (st.fC - (sec (projTD (constComb - (qzOf z).1))).1) + u) := by
      ext <;> simp
    rw [hpair, map_add]
    change S x j + T ((st.fL x - ΔL x) + (st.fC - (sec (projTD (constComb - (qzOf z).1))).1) + u) j + cvec j = _
    simp only [map_add, map_sub, linComb, constComb, LinearMap.add_apply, LinearMap.comp_apply,
      Pi.add_apply, Pi.sub_apply]
    abel
  rw [hsplit]
  have hTu : T u = 0 := huE.2
  have hTΔL : T (ΔL x) = (projTD (linComb x)).1 := hsec (projTD (linComb x))
  have hTΔC : T (sec (projTD (constComb - (qzOf z).1))).1 = (projTD (constComb - (qzOf z).1)).1 :=
    hsec (projTD (constComb - (qzOf z).1))
  rw [hTu, hTΔL, hTΔC, add_zero]
  have hdiff : linComb x + constComb - (projTD (linComb x)).1 - (projTD (constComb - (qzOf z).1)).1 =
      (qzOf z).1 := by
    have hcomb : (projTD (linComb x)).1 + (projTD (constComb - (qzOf z).1)).1 =
        (projTD (linComb x + constComb - (qzOf z).1)).1 := by
      have : linComb x + (constComb - (qzOf z).1) = linComb x + constComb - (qzOf z).1 := by abel
      rw [← this, map_add]
      rfl
    have hsum := proj_add_symm hQ (linComb x + constComb - (qzOf z).1)
    have hprojQ_zero : projQ (linComb x + constComb - (qzOf z).1) = 0 := by
      rw [map_sub, ← hqz, Submodule.projectionOnto_apply_left hQ.symm (qzOf z), sub_self]
    have hprojTD_eq : (projTD (linComb x + constComb - (qzOf z).1)).1 =
        linComb x + constComb - (qzOf z).1 := by
      have h0 : (projQ (linComb x + constComb - (qzOf z).1)).1 = 0 := congrArg Subtype.val hprojQ_zero
      change (projTD (linComb x + constComb - (qzOf z).1)).1 + (projQ (linComb x + constComb - (qzOf z).1)).1 =
        linComb x + constComb - (qzOf z).1 at hsum
      rw [h0, add_zero] at hsum
      exact hsum
    have : linComb x + constComb - (projTD (linComb x)).1 - (projTD (constComb - (qzOf z).1)).1 =
        linComb x + constComb - ((projTD (linComb x)).1 + (projTD (constComb - (qzOf z).1)).1) := by abel
    rw [this, hcomb, hprojTD_eq]
    abel
  rw [hdiff]

end PEqualNP.Outside.L_pcx_425_aux

theorem PEqualNP.Outside.L_pcx_425 :
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n k t r : ℕ) (A : Type),
  let X := Fin n → K
  let U := Fin k → K
  let Y := Fin t → K
  let H := List (List K)
  ∀ (P : Set X) (ok : X → A → Prop) (M : A → U →ₗ[K] Y)
    (width : ℕ → ℕ) (due : A → Fin (r+1)),
    let trace := fun (len : H → ℕ) (value : H → ℕ → K) =>
      (List.range r).foldl (fun (h : H) (_ : ℕ) =>
        h ++ [List.ofFn (fun j : Fin (len h) => value h j.val)]) []
    (∃ (ask : H → ℕ → (X × U) →ₗ[K] K) (off : H → ℕ → K) (out : H → Option (A × Y)),
      ∀ x ∈ P, ∀ u : U,
        let path := trace (fun h => width h.length) (fun h j => ask h j (x,u) + off h j)
        (∃ d ≤ r, (out (path.take d)).isSome = true) ∧
        ∀ d ≤ r, ∀ i y, out (path.take d) = some (i,y) → d ≤ (due i).val ∧ ok x i ∧ y = M i u) ↔
    ∃ (len : H → ℕ) (ask : H → ℕ → X →ₗ[K] K) (off : H → ℕ → K) (out : H → Option A)
      (D E : H → Submodule K U),
      D [] = ⊤ ∧
      (∀ h, E h ≤ D h ∧
        len h + (Module.finrank K (D h) - Module.finrank K (E h)) ≤ width h.length ∧
        ∀ z : List K, z.length = len h → D (h ++ [z]) = E h) ∧
      ∀ x ∈ P,
        let path := trace len (fun h j => ask h j x + off h j)
        (∃ d ≤ r, (out (path.take d)).isSome = true) ∧
        ∀ d ≤ r, ∀ i, out (path.take d) = some i →
          d ≤ (due i).val ∧ ok x i ∧ D (path.take d) ≤ LinearMap.ker (M i) := by
  intro K _ _ _ n k t r A X U Y H P ok M width due trace
  open PEqualNP.Outside.L_pcx_425_aux in
  constructor
  · rintro ⟨ask, off, out, hspec⟩
    let initSt : SimState K n k := ⟨[], ⊤, 0, 0⟩
    let stepSt : SimState K n k → List K → SimState K n k :=
      fun st z => (buildStep width ask off st).2.2.2.2.1 z
    let run : H → SimState K n k := fun h => h.foldl stepSt initSt
    have hrun_len : ∀ h : H, (run h).sim.length = h.length := by
      intro h
      induction h using List.reverseRecOn with
      | nil => rfl
      | append_singleton h z ih =>
        have hstep : run (h ++ [z]) = stepSt (run h) z := by
          dsimp only [run]; rw [List.foldl_append]; rfl
        rw [hstep]
        have h1 := ((buildStep width ask off (run h)).2.2.2.2.2.2.2.1 z).2.1
        simp [stepSt, h1, ih]
    let len : H → ℕ := fun h => (buildStep width ask off (run h)).1
    let E : H → Submodule K U := fun h => (buildStep width ask off (run h)).2.1
    let ask' : H → ℕ → X →ₗ[K] K := fun h => (buildStep width ask off (run h)).2.2.1
    let off' : H → ℕ → K := fun h => (buildStep width ask off (run h)).2.2.2.1
    let D : H → Submodule K U := fun h => (run h).D
    let out' : H → Option A := fun h => (out (run h).sim).map Prod.fst
    refine ⟨len, ask', off', out', D, E, rfl, ?_, ?_⟩
    · intro h
      have hb := (buildStep width ask off (run h)).2.2.2.2.2
      refine ⟨hb.1, ?_, fun z _ => ?_⟩
      · rw [← hrun_len h]; exact hb.2.1
      · have hstep : run (h ++ [z]) = stepSt (run h) z := by
          dsimp only [run]; rw [List.foldl_append]; rfl
        change (run (h ++ [z])).D = E h
        rw [hstep]
        exact (hb.2.2.1 z).1
    · intro x hxP
      let path' := trace len (fun h j => ask' h j x + off' h j)
      have hsim_eq : ∀ d : ℕ, d ≤ r → ∀ u ∈ D (traceAux len (fun h j => ask' h j x + off' h j) d),
          let h' := traceAux len (fun h j => ask' h j x + off' h j) d
          let st := run h'
          traceAux (fun h => width h.length) (fun h j => ask h j (x, st.fL x + st.fC + u) + off h j) d = st.sim := by
        intro d
        induction d with
        | zero => intro _ _ _; rfl
        | succ d ih =>
          intro hdr u hu
          let h' := traceAux len (fun h j => ask' h j x + off' h j) d
          let z := List.ofFn (fun j : Fin (len h') => ask' h' j.val x + off' h' j.val)
          have hsucc : traceAux len (fun h j => ask' h j x + off' h j) (d + 1) = h' ++ [z] := rfl
          have hrun_succ : run (h' ++ [z]) = stepSt (run h') z := by
            dsimp only [run]; rw [List.foldl_append]; rfl
          have huE : u ∈ E h' := by
            change u ∈ (run (h' ++ [z])).D at hu
            rw [hrun_succ] at hu
            have := ((buildStep width ask off (run h')).2.2.2.2.2.2.2.1 z).1
            simpa [stepSt, this] using hu
          have hb_step := (buildStep width ask off (run h')).2.2.2.2.2.2.2.2 x u huE
          have hmemD : (run (h' ++ [z])).fL x + (run (h' ++ [z])).fC + u - ((run h').fL x + (run h').fC) ∈ D h' := by
            rw [hrun_succ]
            exact hb_step.1
          set v : U := (run (h' ++ [z])).fL x + (run (h' ++ [z])).fC + u - ((run h').fL x + (run h').fC)
          have hvu : (run h').fL x + (run h').fC + v = (run (h' ++ [z])).fL x + (run (h' ++ [z])).fC + u := by
            simp only [v]; abel
          have hprev := ih (Nat.le_of_succ_le hdr) v hmemD
          dsimp only at hprev
          rw [hvu] at hprev
          change traceAux (fun h => width h.length)
            (fun h j => ask h j (x, (run (h' ++ [z])).fL x + (run (h' ++ [z])).fC + u) + off h j) (d + 1) =
            (run (h' ++ [z])).sim
          simp only [traceAux]
          rw [hprev, hrun_succ]
          exact hb_step.2.symm
      have hpath'_take : ∀ d ≤ r, path'.take d = traceAux len (fun h j => ask' h j x + off' h j) d := by
        intro d hdr
        have htr : path' = traceAux len (fun h j => ask' h j x + off' h j) r := by
          dsimp only [path', trace]; exact foldl_range_eq_traceAux len (fun h j => ask' h j x + off' h j) r
        rw [htr, traceAux_take _ _ hdr]
      constructor
      · let stR := run (traceAux len (fun h j => ask' h j x + off' h j) r)
        let u0 : U := stR.fL x + stR.fC
        have hsp := hspec x hxP u0
        rcases hsp.1 with ⟨d, hdr, hsome⟩
        refine ⟨d, hdr, ?_⟩
        rw [hpath'_take d hdr]
        have hsim_r := hsim_eq r le_rfl 0 (D _).zero_mem
        simp only [add_zero] at hsim_r
        have horig_take : ∀ s ≤ r,
            (trace (fun h => width h.length) (fun h j => ask h j (x, u0) + off h j)).take s =
              traceAux (fun h => width h.length) (fun h j => ask h j (x, u0) + off h j) s := by
          intro s hsr
          have htr : trace (fun h => width h.length) (fun h j => ask h j (x, u0) + off h j) =
              traceAux (fun h => width h.length) (fun h j => ask h j (x, u0) + off h j) r := by
            dsimp only [trace, H]; exact foldl_range_eq_traceAux (fun h => width h.length) (fun h j => ask h j (x, u0) + off h j) r
          rw [htr, traceAux_take _ _ hsr]
        have hsim_prefix : ∀ (a b : H), List.IsPrefix a b → List.IsPrefix (run a).sim (run b).sim := by
          intro a b hab
          rcases hab with ⟨c, rfl⟩
          induction c using List.reverseRecOn with
          | nil => simp
          | append_singleton c w ihc =>
            rw [← List.append_assoc]
            have hstep : run ((a ++ c) ++ [w]) = stepSt (run (a ++ c)) w := by
              dsimp only [run]; rw [List.foldl_append]; rfl
            rw [hstep]
            have hpre_w := ((buildStep width ask off (run (a ++ c))).2.2.2.2.2.2.2.1 w).2.2
            exact ihc.trans hpre_w
        have hpre_r : List.IsPrefix (traceAux len (fun h j => ask' h j x + off' h j) d)
            (traceAux len (fun h j => ask' h j x + off' h j) r) := by
          rw [← traceAux_take len (fun h j => ask' h j x + off' h j) hdr]
          exact List.take_prefix d _
        have hpre_sim := hsim_prefix _ _ hpre_r
        have htake_sim : (run (traceAux len (fun h j => ask' h j x + off' h j) r)).sim.take d =
            (run (traceAux len (fun h j => ask' h j x + off' h j) d)).sim := by
          rcases hpre_sim with ⟨tail, htail⟩
          rw [← htail, List.take_append_of_le_length]
          · rw [List.take_of_length_le]
            rw [hrun_len, traceAux_length]
          · rw [hrun_len, traceAux_length]
        have horig_d : (trace (fun h => width h.length) (fun h j => ask h j (x, u0) + off h j)).take d =
            (run (traceAux len (fun h j => ask' h j x + off' h j) d)).sim := by
          rw [horig_take d hdr, ← traceAux_take _ _ hdr, hsim_r, htake_sim]
        rw [horig_d] at hsome
        simp only [out', Option.isSome_map]
        exact hsome
      · intro d hdr i hi
        rw [hpath'_take d hdr] at hi ⊢
        simp only [out', Option.map_eq_some_iff] at hi
        rcases hi with ⟨⟨i', y⟩, hout_eq, rfl⟩
        let hd := traceAux len (fun h j => ask' h j x + off' h j) d
        have hsp0 := hspec x hxP ((run hd).fL x + (run hd).fC)
        have hsim0 := hsim_eq d hdr 0 (D hd).zero_mem
        simp only [add_zero] at hsim0
        have htake0 : (trace (fun h => width h.length)
            (fun h j => ask h j (x, (run hd).fL x + (run hd).fC) + off h j)).take d = (run hd).sim := by
          have htr : trace (fun h => width h.length) (fun h j => ask h j (x, (run hd).fL x + (run hd).fC) + off h j) =
              traceAux (fun h => width h.length) (fun h j => ask h j (x, (run hd).fL x + (run hd).fC) + off h j) r := by
            dsimp only [trace, H]; exact foldl_range_eq_traceAux (fun h => width h.length) (fun h j => ask h j (x, (run hd).fL x + (run hd).fC) + off h j) r
          rw [htr, traceAux_take _ _ hdr]
          exact hsim0
        rw [← htake0] at hout_eq
        have hres0 := hsp0.2 d hdr i' y hout_eq
        refine ⟨hres0.1, hres0.2.1, fun u hu => ?_⟩
        have hspu := hspec x hxP ((run hd).fL x + (run hd).fC + u)
        have hsimu := hsim_eq d hdr u hu
        have htakeu : (trace (fun h => width h.length)
            (fun h j => ask h j (x, (run hd).fL x + (run hd).fC + u) + off h j)).take d = (run hd).sim := by
          have htr : trace (fun h => width h.length) (fun h j => ask h j (x, (run hd).fL x + (run hd).fC + u) + off h j) =
              traceAux (fun h => width h.length) (fun h j => ask h j (x, (run hd).fL x + (run hd).fC + u) + off h j) r := by
            dsimp only [trace, H]; exact foldl_range_eq_traceAux (fun h => width h.length) (fun h j => ask h j (x, (run hd).fL x + (run hd).fC + u) + off h j) r
          rw [htr, traceAux_take _ _ hdr]
          exact hsimu
        rw [htake0, ← htakeu] at hout_eq
        have hresu := hspu.2 d hdr i' y hout_eq
        rw [LinearMap.mem_ker]
        have heq : M i' ((run hd).fL x + (run hd).fC + u) = M i' ((run hd).fL x + (run hd).fC) :=
          hresu.2.2.symm.trans hres0.2.2
        rw [map_add] at heq
        have hsub := congrArg (fun z => z - M i' ((run hd).fL x + (run hd).fC)) heq
        simpa using hsub
  · rintro ⟨len, ask', off', out', D, E, hD0, hDE, hspec'⟩
    let φ : ∀ h : H, U →ₗ[K] (Fin (Module.finrank K (D h) - Module.finrank K (E h)) → K) :=
      fun h => Classical.choose (exists_drop_forms (D h) (E h) (hDE h).1)
    have hφ : ∀ h, ∀ u ∈ D h, φ h u = 0 ↔ u ∈ E h :=
      fun h => Classical.choose_spec (exists_drop_forms (D h) (E h) (hDE h).1)
    let decode : H → H := fun h =>
      h.foldl (fun (hsep : H) (row : List K) => hsep ++ [row.take (len hsep)]) []
    have hdec_len : ∀ h : H, (decode h).length = h.length := by
      intro h
      induction h using List.reverseRecOn with
      | nil => rfl
      | append_singleton h row ih =>
        have ha : decode (h ++ [row]) = decode h ++ [row.take (len (decode h))] := by
          dsimp only [decode]; rw [List.foldl_append]; rfl
        rw [ha, List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih]
    have hdec_append : ∀ (h : H) (row : List K),
        decode (h ++ [row]) = decode h ++ [row.take (len (decode h))] := by
      intro h row
      dsimp only [decode]; rw [List.foldl_append]; rfl
    let ask : H → ℕ → (X × U) →ₗ[K] K := fun h j =>
      let hsep := decode h
      if j < len hsep then (ask' hsep j).comp (LinearMap.fst K X U)
      else if hj : j - len hsep < Module.finrank K (D hsep) - Module.finrank K (E hsep) then
        ((LinearMap.proj ⟨j - len hsep, hj⟩).comp (φ hsep)).comp (LinearMap.snd K X U)
      else 0
    let off : H → ℕ → K := fun h j =>
      let hsep := decode h
      if j < len hsep then off' hsep j else 0
    let matchU : H → U → Prop := fun h u =>
      ∀ (s : Fin h.length)
        (j : Fin (Module.finrank K (D (decode (h.take s.val))) - Module.finrank K (E (decode (h.take s.val))))),
        (h.get s).getD (len (decode (h.take s.val)) + j.val) 0 = φ (decode (h.take s.val)) u j
    let out : H → Option (A × Y) := fun h =>
      match out' (decode h) with
      | none => none
      | some i =>
        if hex : ∃ u0 : U, matchU h u0 then some (i, M i (Classical.choose hex))
        else some (i, 0)
    refine ⟨ask, off, out, fun x hxP u => ?_⟩
    let path := trace (fun h => width h.length) (fun h j => ask h j (x, u) + off h j)
    let path' := trace len (fun h j => ask' h j x + off' h j)
    have hdec_trace : ∀ d : ℕ,
        decode (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d) =
          traceAux len (fun h j => ask' h j x + off' h j) d := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        simp only [traceAux]
        rw [hdec_append, ih]
        congr 1
        congr 1
        set h0 := traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d
        set hs := traceAux len (fun h j => ask' h j x + off' h j) d
        have hlen_le : len hs ≤ width h0.length := by
          have h1 := (hDE hs).2.1
          have h2 : h0.length = hs.length := by rw [traceAux_length, traceAux_length]
          rw [h2]; omega
        apply List.ext_getElem
        · simp [hlen_le]
        · intro j hj1 hj2
          simp only [List.length_ofFn] at hj2
          simp only [List.getElem_take, List.getElem_ofFn, ask, off, ih, hj2, ↓reduceIte,
            LinearMap.comp_apply, LinearMap.fst_apply]
    have hmatch_trace : ∀ d : ℕ,
        matchU (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d) u := by
      intro d
      dsimp only [matchU]
      generalize hhd : traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d = hd
      have htake_all : ∀ k ≤ d, hd.take k = traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) k := by
        intro k hkd; rw [← hhd]; exact traceAux_take _ _ hkd
      have hhd_len : hd.length = d := by rw [← hhd, traceAux_length]
      intro s j
      have hs_lt : s.val < d := by have := s.isLt; omega
      have htake_s : hd.take s.val = traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) s.val :=
        htake_all s.val (Nat.le_of_lt hs_lt)
      have htake_s1 : hd.take (s.val + 1) =
          traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (s.val + 1) :=
        htake_all (s.val + 1) hs_lt
      have hget_s : hd.get s =
          List.ofFn (fun i : Fin (width (hd.take s.val).length) =>
            ask (hd.take s.val) i.val (x, u) + off (hd.take s.val) i.val) := by
        rw [List.get_eq_getElem]
        have h1 : (hd.take (s.val + 1))[s.val]'(by rw [htake_s1, traceAux_length]; omega) = hd[s.val]'s.isLt :=
          List.getElem_take
        rw [← h1]
        have h2 : ∀ (L : H) (hL : L = hd.take s.val ++ [List.ofFn (fun i : Fin (width (hd.take s.val).length) =>
            ask (hd.take s.val) i.val (x, u) + off (hd.take s.val) i.val)]) (hlt : s.val < L.length),
            L[s.val]'hlt = List.ofFn (fun i : Fin (width (hd.take s.val).length) =>
              ask (hd.take s.val) i.val (x, u) + off (hd.take s.val) i.val) := by
          rintro L rfl hlt
          have hlen0 : (hd.take s.val).length = s.val := by rw [htake_s, traceAux_length]
          rw [List.getElem_append_right (by omega)]
          exact List.getElem_singleton _
        exact h2 _ (by rw [htake_s1, traceAux, ← htake_s]) _
      rw [hget_s]
      let hsep := decode (hd.take s.val)
      have hj_lt : j.val < Module.finrank K (D hsep) - Module.finrank K (E hsep) := j.isLt
      have hlen_w : len hsep + j.val < width (hd.take s.val).length := by
        have h1 := (hDE hsep).2.1
        have h2 : (hd.take s.val).length = hsep.length := (hdec_len _).symm
        rw [h2]; omega
      have hnotlt : ¬ (len hsep + j.val < len hsep) := by omega
      have hsub_eq : len hsep + j.val - len hsep = j.val := by omega
      have hgetD : (List.ofFn (fun i : Fin (width (hd.take s.val).length) =>
          ask (hd.take s.val) i.val (x, u) + off (hd.take s.val) i.val)).getD (len hsep + j.val) 0 =
          ask (hd.take s.val) (len hsep + j.val) (x, u) + off (hd.take s.val) (len hsep + j.val) := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlen_w), List.getElem_ofFn]
      rw [hgetD]
      simp only [ask, off, hsep, hnotlt, ↓reduceIte, hsub_eq, hj_lt, ↓reduceDIte, add_zero,
        LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.proj_apply]
    have hker_match : ∀ d : ℕ, ∀ u0 : U,
        matchU (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d) u0 →
        u - u0 ∈ D (traceAux len (fun h j => ask' h j x + off' h j) d) := by
      intro d u0 hm0
      induction d with
      | zero =>
        simp [traceAux, hD0]
      | succ d ih =>
        have hprev_m0 : matchU (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d) u0 := by
          intro s j
          have hs_lt : s.val < d := by simpa [traceAux_length] using s.isLt
          have hs1 : s.val < (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)).length := by
            have hlen1 := traceAux_length (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)
            omega
          have hm := hm0 ⟨s.val, hs1⟩
          have htake_eq : (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)).take s.val =
              (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d).take s.val := by
            rw [traceAux_take _ _ (Nat.le_of_lt (Nat.lt_succ_of_lt hs_lt)), traceAux_take _ _ (Nat.le_of_lt hs_lt)]
          have hget_eq : (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)).get ⟨s.val, hs1⟩ =
              (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d).get s := by
            simp only [traceAux, List.get_eq_getElem]
            rw [List.getElem_append_left s.isLt]
          rw [htake_eq, hget_eq] at hm
          exact hm j
        have hmemD : u - u0 ∈ D (traceAux len (fun h j => ask' h j x + off' h j) d) := ih hprev_m0
        have hd_lt : d < (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)).length := by
          rw [traceAux_length]; omega
        have hmu := hmatch_trace (d + 1) ⟨d, hd_lt⟩
        have hm0' := hm0 ⟨d, hd_lt⟩
        have htake_d : (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)).take d =
            traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d :=
          traceAux_take _ _ (Nat.le_succ d)
        have hφ_eq : φ (traceAux len (fun h j => ask' h j x + off' h j) d) (u - u0) = 0 := by
          have hheq : decode ((traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) (d + 1)).take d) =
              traceAux len (fun h j => ask' h j x + off' h j) d := by
            rw [htake_d, hdec_trace]
          have htrans : ∀ (h1 h2 : H) (heq : h1 = h2),
              (∀ j : Fin (Module.finrank K (D h1) - Module.finrank K (E h1)), φ h1 u j = φ h1 u0 j) →
              φ h2 (u - u0) = 0 := by
            rintro h1 _ rfl h
            ext j
            rw [map_sub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
            exact h j
          exact htrans _ _ hheq fun j => (hmu j).symm.trans (hm0' j)
        have hmemE : u - u0 ∈ E (traceAux len (fun h j => ask' h j x + off' h j) d) :=
          (hφ _ (u - u0) hmemD).mp hφ_eq
        simp only [traceAux]
        rw [(hDE _).2.2 _ (by simp)]
        exact hmemE
    have hsp := hspec' x hxP
    have htake_orig : ∀ d ≤ r, path.take d =
        traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d := by
      intro d hdr
      have htr : path = traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) r := by
        dsimp only [path, trace, H]; exact foldl_range_eq_traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) r
      rw [htr, traceAux_take _ _ hdr]
    have htake_sep : ∀ d ≤ r, path'.take d =
        traceAux len (fun h j => ask' h j x + off' h j) d := by
      intro d hdr
      have htr : path' = traceAux len (fun h j => ask' h j x + off' h j) r := by
        dsimp only [path', trace, H]; exact foldl_range_eq_traceAux len (fun h j => ask' h j x + off' h j) r
      rw [htr, traceAux_take _ _ hdr]
    constructor
    · rcases hsp.1 with ⟨d, hdr, hsome⟩
      refine ⟨d, hdr, ?_⟩
      rw [htake_sep d hdr] at hsome
      rw [htake_orig d hdr]
      dsimp only [out]
      rw [hdec_trace d]
      cases hout : out' (traceAux len (fun h j => ask' h j x + off' h j) d) with
      | none => rw [hout] at hsome; simp at hsome
      | some i =>
        simp only
        split_ifs <;> rfl
    · intro d hdr i y hout_eq
      rw [htake_orig d hdr] at hout_eq
      dsimp only [out] at hout_eq
      rw [hdec_trace d] at hout_eq
      cases hout' : out' (traceAux len (fun h j => ask' h j x + off' h j) d) with
      | none => rw [hout'] at hout_eq; simp at hout_eq
      | some i' =>
        rw [hout'] at hout_eq
        have hex : ∃ u0 : U, matchU (traceAux (fun h => width h.length) (fun h j => ask h j (x, u) + off h j) d) u0 :=
          ⟨u, hmatch_trace d⟩
        simp only at hout_eq
        rw [dif_pos hex] at hout_eq
        have hpair := Option.some.inj hout_eq
        have hi_eq : i' = i := congrArg Prod.fst hpair
        have hy_eq : M i' (Classical.choose hex) = y := congrArg Prod.snd hpair
        subst hi_eq
        rw [← htake_sep d hdr] at hout'
        have hres := hsp.2 d hdr i' hout'
        refine ⟨hres.1, hres.2.1, ?_⟩
        rw [← hy_eq]
        have hdiff : u - Classical.choose hex ∈ D (path'.take d) := by
          rw [htake_sep d hdr]
          exact hker_match d (Classical.choose hex) (Classical.choose_spec hex)
        have hker := hres.2.2 hdiff
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hker
        exact hker.symm
