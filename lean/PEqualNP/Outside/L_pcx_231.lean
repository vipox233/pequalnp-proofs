import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_231_aux.Cube

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Pat (n : ℕ) := Fin (n - 1) → Bool
abbrev Row (n : ℕ) := Fin n × Pat n

def rot {n : ℕ} (hn : 0 < n) (i : Fin n) : Equiv.Perm (Fin n) :=
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  Equiv.addLeft i

def last {n : ℕ} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

def missing {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n := rot hn i (last hn)

theorem missing_bij {n : ℕ} (hn : 0 < n) : Function.Bijective (missing hn) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  change Function.Bijective (fun i => i + last hn)
  exact (Equiv.addRight (last hn)).bijective

def window {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Word n) : Pat n :=
  fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

theorem window_at {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Word n) (j : Fin (n - 1)) :
    window hn i x j = x (rot hn i (Fin.castLE (by omega) j)) := rfl

theorem window_eq_iff {n : ℕ} (hn : 0 < n) (i : Fin n) (x y : Word n) :
    window hn i x = window hn i y ↔ ∀ k, k ≠ missing hn i → x k = y k := by
  constructor
  · intro hw k hk
    obtain ⟨a, rfl⟩ := (rot hn i).surjective k
    have ha : a.val < n - 1 := by
      by_contra h
      have e : a = last hn := Fin.ext (by simp only [last]; omega)
      exact hk (congrArg (rot hn i) e)
    exact congrFun hw ⟨a.val, ha⟩
  · intro h
    funext j
    rw [window_at, window_at]
    apply h
    intro he
    have h' := (rot hn i).injective he
    have hval := congrArg Fin.val h'
    change j.val = n - 1 at hval
    omega

def fill {n : ℕ} (hn : 0 < n) (i : Fin n) (p : Pat n) (b : Bool) : Word n :=
  fun k => if h : ((rot hn i).symm k).val < n - 1 then p ⟨_, h⟩ else b

theorem fill_window {n : ℕ} (hn : 0 < n) (i : Fin n) (p : Pat n) (b : Bool) :
    window hn i (fill hn i p b) = p := by
  funext j
  rw [window_at]
  simp only [fill, Equiv.symm_apply_apply, Fin.val_castLE, j.isLt, dite_true]

theorem fill_missing {n : ℕ} (hn : 0 < n) (i : Fin n) (p : Pat n) (b : Bool) :
    fill hn i p b (missing hn i) = b := by
  simp [fill, missing, last]

theorem fill_of_window {n : ℕ} (hn : 0 < n) (i : Fin n) (p : Pat n) (x : Word n)
    (hx : window hn i x = p) : fill hn i p (x (missing hn i)) = x := by
  funext k
  by_cases hk : k = missing hn i
  · subst k
    exact fill_missing ..
  · exact (window_eq_iff hn i _ _).mp ((fill_window hn i p _).trans hx.symm) k hk

noncomputable def fiber {n : ℕ} (hn : 0 < n) (r : Row n) : Finset (Word n) := by
  classical
  exact Finset.univ.filter (fun x => window hn r.1 x = r.2)

theorem mem_fiber {n : ℕ} (hn : 0 < n) (r : Row n) (x : Word n) :
    x ∈ fiber hn r ↔ window hn r.1 x = r.2 := by
  classical
  simp [fiber]

theorem fiber_pair {n : ℕ} (hn : 0 < n) (r : Row n) :
    fiber hn r = {fill hn r.1 r.2 false, fill hn r.1 r.2 true} := by
  classical
  ext x
  rw [mem_fiber, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hf := (fill_of_window hn r.1 r.2 x h).symm
    cases hb : x (missing hn r.1)
    · exact Or.inl (by simpa only [hb] using hf)
    · exact Or.inr (by simpa only [hb] using hf)
  · rintro (rfl | rfl) <;> exact fill_window ..

abbrev Near {n : ℕ} (x y : Word n) : Prop :=
  (Finset.univ.filter (fun k : Fin n => x k ≠ y k)).card ≤ 1

def adj {n : ℕ} (x y : Word n) : Prop := x ≠ y ∧ Near x y

theorem adj_symm {n : ℕ} {x y : Word n} : adj x y → adj y x := by
  intro h
  refine ⟨Ne.symm h.1, ?_⟩
  change (Finset.univ.filter (fun k : Fin n => y k ≠ x k)).card ≤ 1
  have he : (Finset.univ.filter (fun k : Fin n => y k ≠ x k)) =
      Finset.univ.filter (fun k : Fin n => x k ≠ y k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_comm
  rw [he]
  exact h.2

theorem adj_irrefl {n : ℕ} (x : Word n) : ¬ adj x x := fun h => h.1 rfl

theorem adj_of_diff {n : ℕ} {x y : Word n} (k : Fin n) (hk : x k ≠ y k)
    (h : ∀ j ≠ k, x j = y j) : adj x y := by
  refine ⟨fun e => hk (congrFun e k), ?_⟩
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  replace ha := (Finset.mem_filter.mp ha).2
  replace hb := (Finset.mem_filter.mp hb).2
  have ea : a = k := by by_contra hn; exact ha (h a hn)
  have eb : b = k := by by_contra hn; exact hb (h b hn)
  exact ea.trans eb.symm

theorem right_fill_adj {n : ℕ} (hn : 0 < n) (i : Fin n) (p : Pat n) :
    adj (fill hn i p false) (fill hn i p true) := by
  apply adj_of_diff (missing hn i)
  · rw [fill_missing, fill_missing]; decide
  · apply (window_eq_iff hn i _ _).mp
    rw [fill_window, fill_window]

theorem adj_has_neighbor {n : ℕ} (hn : 0 < n) (x : Word n) : ∃ y, adj x y := by
  let i : Fin n := ⟨0, hn⟩
  let y := fill hn i (window hn i x) (!(x (missing hn i)))
  refine ⟨y, adj_of_diff (missing hn i) ?_ ?_⟩
  · change x (missing hn i) ≠ fill hn i (window hn i x) (!(x (missing hn i))) (missing hn i)
    rw [fill_missing]
    cases x (missing hn i) <;> decide
  · apply (window_eq_iff hn i _ _).mp
    exact (fill_window hn i _ _).symm

theorem fiber_inj {n : ℕ} (hn : 0 < n) : Function.Injective (fiber hn) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ e
  have hmem (b : Bool) : fill hn i p b ∈ fiber hn (j, q) := by
    rw [← e, mem_fiber]
    exact fill_window ..
  have hw : window hn j (fill hn i p false) = window hn j (fill hn i p true) :=
    ((mem_fiber hn (j, q) _).mp (hmem false)).trans (((mem_fiber hn (j, q) _).mp (hmem true)).symm)
  have hm : missing hn i = missing hn j := by
    by_contra h
    have z := (window_eq_iff hn j _ _).mp hw (missing hn i) h
    rw [fill_missing, fill_missing] at z
    contradiction
  have hij := (missing_bij hn).injective hm
  subst j
  have hpq : p = q := (fill_window hn i p false).symm.trans ((mem_fiber hn (i, q) _).mp (hmem false))
  subst q
  rfl

theorem fiber_of_adj {n : ℕ} (hn : 0 < n) {x y : Word n} (h : adj x y) :
    ∃ r : Row n, fiber hn r = {x, y} := by
  classical
  obtain ⟨k, hk⟩ := not_forall.mp (fun hxy : ∀ k, x k = y k => h.1 (funext hxy))
  obtain ⟨i, hi⟩ := (missing_bij hn).surjective k
  have hx (j : Fin n) (hj : j ≠ missing hn i) : x j = y j := by
    by_contra hnxy
    apply hj
    rw [hi]
    exact Finset.card_le_one_iff.mp h.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnxy⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  let p := window hn i x
  have hy : window hn i y = p := ((window_eq_iff hn i x y).mpr hx).symm
  refine ⟨(i, p), ?_⟩
  have fx := (fill_of_window hn i p x rfl).symm
  have fy := (fill_of_window hn i p y hy).symm
  have hd : x (missing hn i) ≠ y (missing hn i) := hi.symm ▸ hk
  rw [fiber_pair]
  cases hb : x (missing hn i) <;> cases hc : y (missing hn i)
  · exact (hd (hb.trans hc.symm)).elim
  · simp only [hb] at fx
    simp only [hc] at fy
    exact congrArg₂ (fun a b => ({a, b} : Finset (Word n))) fx.symm fy.symm
  · simp only [hb] at fx
    simp only [hc] at fy
    rw [Finset.pair_comm]
    exact congrArg₂ (fun a b => ({a, b} : Finset (Word n))) fx.symm fy.symm
  · exact (hd (hb.trans hc.symm)).elim

end PEqualNP.Outside.L_pcx_231_aux.Cube

namespace PEqualNP.Outside.L_pcx_231_aux.Stars

variable {α : Type*}

def edge [DecidableEq α] (Adj : α → α → Prop) (e : Finset α) : Prop :=
  ∃ u v, Adj u v ∧ e = {u, v}

def edgeCovers (A : Finset (Finset α)) : Prop :=
  ∀ x, ∃ e ∈ A, x ∈ e

def edgeMinimal [DecidableEq α] (A : Finset (Finset α)) : Prop :=
  edgeCovers A ∧ ∀ e ∈ A, ¬ edgeCovers (A.erase e)

def dominates (Adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ x, ∃ y ∈ S, x = y ∨ Adj x y

variable [Fintype α] [DecidableEq α] {Adj : α → α → Prop}

theorem dominating_of_edgeMinimal
    (hsym : ∀ ⦃x y⦄, Adj x y → Adj y x) (hirr : ∀ x, ¬ Adj x x)
    {A : Finset (Finset α)} (hvalid : ∀ e ∈ A, edge Adj e) (hmin : edgeMinimal A) :
    ∃ S : Finset α, dominates Adj S ∧ A.card + S.card = Fintype.card α := by
  classical
  have hprivate (e : Finset α) (he : e ∈ A) :
      ∃ x ∈ e, ∀ f ∈ A, x ∈ f → f = e := by
    by_contra hn
    apply hmin.2 e he
    intro x
    by_contra hx
    have huniq (f : Finset α) (hf : f ∈ A) (hxf : x ∈ f) : f = e := by
      by_contra hfe
      exact hx ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hxf⟩
    obtain ⟨f, hf, hxf⟩ := hmin.1 x
    exact hn ⟨x, huniq f hf hxf ▸ hxf, huniq⟩
  have horient (e : {e : Finset α // e ∈ A}) :
      ∃ l c, Adj l c ∧ e.val = {l, c} ∧ ∀ f ∈ A, l ∈ f → f = e.val := by
    obtain ⟨x, hx, hp⟩ := hprivate e.val e.property
    obtain ⟨u, v, huv, he⟩ := hvalid e.val e.property
    have hxu : x = u ∨ x = v := by
      simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hxu with h | h
    · subst x
      exact ⟨u, v, huv, he, hp⟩
    · subst x
      have hswap : ({u, v} : Finset α) = {v, u} := by
        apply Finset.ext
        intro w
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
      exact ⟨v, u, hsym huv, he.trans hswap, hp⟩
  choose leaf center hadj hpair huniq using horient
  have hlmem (e : {e : Finset α // e ∈ A}) : leaf e ∈ e.val := by
    rw [hpair e]
    simp
  have hinj : Function.Injective leaf := by
    intro e f hef
    apply Subtype.ext
    apply huniq f e.val e.property
    rw [← hef]
    exact hlmem e
  let L := A.attach.image leaf
  have hcenter (e : {e : Finset α // e ∈ A}) : center e ∉ L := by
    intro he
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp he
    have hce : center e ∈ e.val := by
      rw [hpair e]
      simp
    have hef : e = f := Subtype.ext (huniq f e.val e.property (hf.symm ▸ hce))
    subst f
    exact hirr (center e) (by simpa only [hf] using hadj e)
  let S := Finset.univ \ L
  have hS (x : α) : x ∈ S ↔ x ∉ L := by simp [S]
  refine ⟨S, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ L
    · obtain ⟨e, _, hxe⟩ := Finset.mem_image.mp hx
      exact ⟨center e, (hS _).2 (hcenter e), Or.inr (hxe ▸ hadj e)⟩
    · exact ⟨x, (hS x).2 hx, Or.inl rfl⟩
  · have hLcard : L.card = A.card := by
      change (A.attach.image leaf).card = A.card
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    rw [← hLcard, Nat.add_comm L.card S.card]
    simpa only [S, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ L)

private theorem exists_surjective_assignment
    (hsym : ∀ ⦃x y⦄, Adj x y → Adj y x) (hirr : ∀ x, ¬ Adj x x)
    (hneigh : ∀ x, ∃ y, Adj x y)
    {S : Finset α} (hdom : dominates Adj S)
    (hmin : ∀ T : Finset α, dominates Adj T → S.card ≤ T.card) :
    ∃ f : α → α, (∀ x, x ∉ S → f x ∈ S ∧ Adj x (f x)) ∧
      (∀ c ∈ S, ∃ x, x ∉ S ∧ f x = c) := by
  classical
  let L := Finset.univ \ S
  have hL (x : α) : x ∈ L ↔ x ∉ S := by simp [L]
  let good (f : α → α) := ∀ x, x ∉ S → f x ∈ S ∧ Adj x (f x)
  have hw : ∀ x, ∃ y ∈ S, x = y ∨ Adj x y := hdom
  choose f₀ h₀mem h₀rel using hw
  have hf₀ : good f₀ := by
    intro x hx
    rcases h₀rel x with h | h
    · exact (hx (h.symm ▸ h₀mem x)).elim
    · exact ⟨h₀mem x, h⟩
  let F := (Finset.univ : Finset (α → α)).filter good
  have hF (g : α → α) : g ∈ F ↔ good g := by simp [F]
  obtain ⟨f, hfF, hmax⟩ :=
    Finset.exists_max_image F (fun g => (L.image g).card) ⟨f₀, (hF f₀).2 hf₀⟩
  have hf := (hF f).1 hfF
  have hserved : S ⊆ L.image f := by
    intro c hc
    by_contra hcI
    have hfne (x : α) (hx : x ∉ S) : f x ≠ c := by
      intro h
      exact hcI (Finset.mem_image.mpr ⟨x, (hL x).2 hx, h⟩)
    obtain ⟨z, hcz⟩ := hneigh c

    have hz : z ∉ S := by
      intro hzS
      have hzc : z ≠ c := by
        intro h
        subst z
        exact hirr c hcz
      have hErase : dominates Adj (S.erase c) := by
        intro x
        by_cases hxc : x = c
        · subst x
          exact ⟨z, Finset.mem_erase.mpr ⟨hzc, hzS⟩, Or.inr hcz⟩
        · by_cases hx : x ∈ S
          · exact ⟨x, Finset.mem_erase.mpr ⟨hxc, hx⟩, Or.inl rfl⟩
          · exact ⟨f x, Finset.mem_erase.mpr ⟨hfne x hx, (hf x hx).1⟩,
              Or.inr (hf x hx).2⟩
      exact (Nat.not_lt_of_ge (hmin _ hErase)) (Finset.card_erase_lt_of_mem hc)
    let d := f z
    have hd : d ∈ S := (hf z hz).1
    have hdc : d ≠ c := hfne z hz
    by_cases hother : ∃ w, w ∉ S ∧ w ≠ z ∧ f w = d
    ·
      obtain ⟨w, hwS, hwz, hwd⟩ := hother
      let g (x : α) := if x = z then c else f x
      have hg : good g := by
        intro x hx
        by_cases hxz : x = z
        · subst x
          simpa only [g, if_pos rfl] using And.intro hc (hsym hcz)
        · simpa only [g, if_neg hxz] using hf x hx
      have hsub : insert c (L.image f) ⊆ L.image g := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_image.mpr ⟨z, (hL z).2 hz, by simp [g]⟩
        · obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
          by_cases hxz : x = z
          · subst x
            have hwy : f w = y := hwd.trans hxy
            exact Finset.mem_image.mpr
              ⟨w, (hL w).2 hwS, by simpa only [g, if_neg hwz] using hwy⟩
          · exact Finset.mem_image.mpr
              ⟨x, hx, by simpa only [g, if_neg hxz] using hxy⟩
      have hinc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hcI] at hinc
      have hle : (L.image g).card ≤ (L.image f).card := hmax g ((hF g).2 hg)
      omega
    ·
      let T := insert z ((S.erase c).erase d)
      have hd' : d ∈ S.erase c := Finset.mem_erase.mpr ⟨hdc, hd⟩
      have hz' : z ∉ (S.erase c).erase d := by
        intro hm
        exact hz (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
      have hzT : z ∈ T := Finset.mem_insert.mpr (Or.inl rfl)
      have hT : dominates Adj T := by
        intro x
        by_cases hxz : x = z
        · exact ⟨z, hzT, Or.inl hxz⟩
        · by_cases hxc : x = c
          · subst x
            exact ⟨z, hzT, Or.inr hcz⟩
          · by_cases hxd : x = d
            · subst x
              exact ⟨z, hzT, Or.inr (hsym (hf z hz).2)⟩
            · by_cases hx : x ∈ S
              · have hm : x ∈ (S.erase c).erase d :=
                  Finset.mem_erase.mpr ⟨hxd, Finset.mem_erase.mpr ⟨hxc, hx⟩⟩
                exact ⟨x, Finset.mem_insert.mpr (Or.inr hm), Or.inl rfl⟩
              · have hfxd : f x ≠ d := fun h => hother ⟨x, hx, hxz, h⟩
                have hm : f x ∈ (S.erase c).erase d := Finset.mem_erase.mpr
                  ⟨hfxd, Finset.mem_erase.mpr ⟨hfne x hx, (hf x hx).1⟩⟩
                exact ⟨f x, Finset.mem_insert.mpr (Or.inr hm), Or.inr (hf x hx).2⟩
      have hcount : T.card + 1 = S.card := by
        change (insert z ((S.erase c).erase d)).card + 1 = S.card
        rw [Finset.card_insert_of_notMem hz', Finset.card_erase_add_one hd',
          Finset.card_erase_add_one hc]
      have hle := hmin T hT
      omega
  refine ⟨f, hf, ?_⟩
  intro c hc
  obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp (hserved hc)
  exact ⟨x, (hL x).1 hx, hxc⟩

theorem edgeMinimal_of_minimum_dominating
    (hsym : ∀ ⦃x y⦄, Adj x y → Adj y x) (hirr : ∀ x, ¬ Adj x x)
    (hneigh : ∀ x, ∃ y, Adj x y)
    {S : Finset α} (hdom : dominates Adj S)
    (hmin : ∀ T : Finset α, dominates Adj T → S.card ≤ T.card) :
    ∃ A : Finset (Finset α), (∀ e ∈ A, edge Adj e) ∧ edgeMinimal A ∧
      A.card + S.card = Fintype.card α := by
  classical
  obtain ⟨f, hf, hserve⟩ := exists_surjective_assignment hsym hirr hneigh hdom hmin
  let L := Finset.univ \ S
  have hL (x : α) : x ∈ L ↔ x ∉ S := by simp [L]
  let E (x : α) : Finset α := {x, f x}
  have hleft (x : α) : x ∈ E x := by simp [E]
  have hright (x : α) : f x ∈ E x := by simp [E]
  have leaf_unique {x y : α} (hx : x ∉ S) (hy : y ∉ S) (hm : x ∈ E y) : x = y := by
    have h : x = y ∨ x = f y := by
      simpa only [E, Finset.mem_insert, Finset.mem_singleton] using hm
    exact h.resolve_right (fun hxy => hx (hxy.symm ▸ (hf y hy).1))
  let A := L.image E
  refine ⟨A, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact ⟨x, f x, (hf x ((hL x).1 hx)).2, rfl⟩
  · refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x ∈ S
      · obtain ⟨y, hy, hyx⟩ := hserve x hx
        exact ⟨E y, Finset.mem_image.mpr ⟨y, (hL y).2 hy, rfl⟩, hyx ▸ hright y⟩
      · exact ⟨E x, Finset.mem_image.mpr ⟨x, (hL x).2 hx, rfl⟩, hleft x⟩
    · intro e he hcover
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨e, he, hxe⟩ := hcover x
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp he).2
      have hxy := leaf_unique ((hL x).1 hx) ((hL y).1 hy) hxe
      subst y
      exact (Finset.mem_erase.mp he).1 rfl
  · have hinj : Set.InjOn E ↑L := by
      intro x hx y hy hxy
      exact leaf_unique ((hL x).1 hx) ((hL y).1 hy) (hxy ▸ hleft x)
    change (L.image E).card + S.card = Fintype.card α
    rw [Finset.card_image_of_injOn hinj]
    simpa only [L, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)

end PEqualNP.Outside.L_pcx_231_aux.Stars

namespace PEqualNP.Outside.L_pcx_231_aux.Cube

open PEqualNP.Outside.L_pcx_231_aux.Stars

theorem image_covers_iff {n : ℕ} (hn : 0 < n) (A : Finset (Row n)) :
    edgeCovers (A.image (fiber hn)) ↔ ∀ x : Word n, ∃ r ∈ A, window hn r.1 x = r.2 := by
  classical
  constructor
  · intro h x
    obtain ⟨e, he, hx⟩ := h x
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp he
    exact ⟨r, hr, (mem_fiber hn r x).mp hx⟩
  · intro h x
    obtain ⟨r, hr, hx⟩ := h x
    exact ⟨fiber hn r, Finset.mem_image_of_mem _ hr, (mem_fiber hn r x).mpr hx⟩

theorem image_minimal_iff {n : ℕ} (hn : 0 < n) (A : Finset (Row n)) :
    edgeMinimal (A.image (fiber hn)) ↔
      (∀ x : Word n, ∃ r ∈ A, window hn r.1 x = r.2) ∧
      ∀ r ∈ A, ¬ (∀ x : Word n, ∃ t ∈ A.erase r, window hn t.1 x = t.2) := by
  classical
  constructor
  · intro h
    refine ⟨(image_covers_iff hn A).mp h.1, ?_⟩
    intro r hr hc
    apply h.2 (fiber hn r) (Finset.mem_image_of_mem _ hr)
    rw [← Finset.image_erase (fiber_inj hn)]
    exact (image_covers_iff hn _).mpr hc
  · intro h
    refine ⟨(image_covers_iff hn A).mpr h.1, ?_⟩
    intro e he hc
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp he
    rw [← Finset.image_erase (fiber_inj hn)] at hc
    exact h.2 r hr ((image_covers_iff hn _).mp hc)

theorem fiber_edge {n : ℕ} (hn : 0 < n) (r : Row n) : edge adj (fiber hn r) := by
  classical
  exact ⟨fill hn r.1 r.2 false, fill hn r.1 r.2 true,
    right_fill_adj hn r.1 r.2, fiber_pair hn r⟩

theorem rows_of_edges {n : ℕ} (hn : 0 < n) (F : Finset (Finset (Word n)))
    (hF : ∀ e ∈ F, edge adj e) : ∃ R : Finset (Row n), R.image (fiber hn) = F := by
  classical
  let R : Finset (Row n) := Finset.univ.filter (fun r => fiber hn r ∈ F)
  refine ⟨R, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hr).2
  · intro he
    obtain ⟨a, b, hab, rfl⟩ := hF e he
    obtain ⟨r, hr⟩ := fiber_of_adj hn hab
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.symm ▸ he⟩, hr⟩

theorem dominates_iff_near {n : ℕ} (S : Finset (Word n)) :
    dominates adj S ↔ ∀ x : Word n, ∃ c ∈ S, Near x c := by
  constructor
  · intro h x
    obtain ⟨c, hc, he | he⟩ := h x
    · subst x
      exact ⟨c, hc, by simp [Near]⟩
    · exact ⟨c, hc, he.2⟩
  · intro h x
    obtain ⟨c, hc, hxc⟩ := h x
    by_cases he : x = c
    · exact ⟨c, hc, Or.inl he⟩
    · exact ⟨c, hc, Or.inr ⟨he, hxc⟩⟩

theorem minimum_dominating (n : ℕ) : ∃ S : Finset (Word n),
    dominates adj S ∧ ∀ T : Finset (Word n), dominates adj T → S.card ≤ T.card := by
  classical
  let family : Finset (Finset (Word n)) := Finset.univ.filter (dominates adj)
  have hne : family.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro x
    exact ⟨x, Finset.mem_univ _, Or.inl rfl⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image family Finset.card hne
  exact ⟨S, (Finset.mem_filter.mp hS).2, fun T ht =>
    hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)⟩

def rowMinimal {n : ℕ} (hn : 0 < n) (A : Finset (Row n)) : Prop :=
  (∀ x : Word n, ∃ r ∈ A, window hn r.1 x = r.2) ∧
    ∀ r ∈ A, ¬ (∀ x : Word n, ∃ t ∈ A.erase r, window hn t.1 x = t.2)

theorem optimal_rows {n : ℕ} (hn : 0 < n) :
    ∃ (A : Finset (Row n)) (S : Finset (Word n)),
      rowMinimal hn A ∧ (∀ B, rowMinimal hn B → B.card ≤ A.card) ∧
      (∀ x : Word n, ∃ c ∈ S, Near x c) ∧
      (∀ T : Finset (Word n), (∀ x : Word n, ∃ c ∈ T, Near x c) → S.card ≤ T.card) ∧
      A.card + S.card = 2 ^ n := by
  classical
  obtain ⟨S, hS, hsmin⟩ := minimum_dominating n
  obtain ⟨F, hF, hFmin, hFin⟩ := edgeMinimal_of_minimum_dominating
    (@adj_symm n) (@adj_irrefl n) (adj_has_neighbor hn) hS hsmin
  obtain ⟨A, hA⟩ := rows_of_edges hn F hF
  have ha : F.card = A.card := by
    rw [← hA, Finset.card_image_of_injective _ (fiber_inj hn)]
  have size : Fintype.card (Word n) = 2 ^ n := by simp
  refine ⟨A, S, (image_minimal_iff hn A).mp (hA.symm ▸ hFmin), ?_,
    (dominates_iff_near S).mp hS, fun T ht => hsmin _ ((dominates_iff_near T).mpr ht), ?_⟩
  · intro B hB
    have he (e) (he : e ∈ B.image (fiber hn)) : edge adj e := by
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
      exact fiber_edge hn r
    obtain ⟨T, ht, hcards⟩ := dominating_of_edgeMinimal (@adj_symm n) (@adj_irrefl n)
      he ((image_minimal_iff hn B).mpr hB)
    rw [Finset.card_image_of_injective _ (fiber_inj hn)] at hcards
    have hmin := hsmin T ht
    omega
  · omega

end PEqualNP.Outside.L_pcx_231_aux.Cube

namespace PEqualNP.Outside.L_pcx_231_aux.Assemble

open PEqualNP.Outside.L_pcx_231_aux.Cube

abbrev Covers {n : ℕ} (S : Finset (Word n)) : Prop := ∀ x, ∃ c ∈ S, Near x c

theorem finish {n : ℕ} (hn : 0 < n) {Pin : Type} [DecidableEq Pin]
    (core : Finset Pin → Prop) (negative : Pin → Prop)
    (realize : ∀ A : Finset (Row n), rowMinimal hn A →
      ∃ P, core P ∧ (∀ e ∈ P, negative e) ∧ P.card = A.card)
    (bound : ∀ Q, core Q → ∃ B : Finset (Row n), rowMinimal hn B ∧ Q.card ≤ B.card)
    (ball : ∀ S : Finset (Word n), Covers S → 2 ^ n ≤ (n + 1) * S.card)
    (three : 3 ≤ n → ∃ T : Finset (Word n), Covers T ∧ 4 * T.card ≤ 2 ^ n)
    (perfect : ∀ r : ℕ, n + 1 = 2 ^ r →
      ∃ T : Finset (Word n), Covers T ∧ (n + 1) * T.card = 2 ^ n) :
    ∃ (P : Finset Pin) (S : Finset (Word n)),
      core P ∧ (∀ l ∈ P, negative l) ∧ (∀ Q, core Q → Q.card ≤ P.card) ∧
      Covers S ∧ (∀ T : Finset (Word n), Covers T → S.card ≤ T.card) ∧ P.card + S.card = 2 ^ n ∧
      (3 ≤ n → 3 * 2 ^ n ≤ 4 * P.card) ∧
      ((∃ r : ℕ, n + 1 = 2 ^ r) → (n + 1) * P.card = n * 2 ^ n) := by
  classical
  obtain ⟨A, S, hA, hmax, hS, hSmin, hsum⟩ := optimal_rows hn
  obtain ⟨P, hP, hneg, hsize⟩ := realize A hA
  have htotal : P.card + S.card = 2 ^ n := hsize.symm ▸ hsum
  refine ⟨P, S, hP, hneg, ?_, hS, hSmin, htotal, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨B, hB, hBQ⟩ := bound Q hQ
    rw [hsize]
    exact hBQ.trans (hmax B hB)
  · intro hn3
    obtain ⟨T, ht, hTcard⟩ := three hn3
    have hsmall := hSmin T ht
    omega
  · rintro ⟨r, hr⟩
    obtain ⟨T, ht, hTcard⟩ := perfect r hr
    have hSmall := Nat.mul_le_mul_left (n + 1) (hSmin T ht)
    have hExact : (n + 1) * S.card = 2 ^ n := le_antisymm (hSmall.trans_eq hTcard) (ball S hS)
    apply Nat.add_right_cancel (m := 2 ^ n)
    calc
      (n + 1) * P.card + 2 ^ n = (n + 1) * (P.card + S.card) := by rw [Nat.mul_add, hExact]
      _ = (n + 1) * 2 ^ n := by rw [htotal]
      _ = n * 2 ^ n + 2 ^ n := by rw [Nat.add_mul, one_mul]

end PEqualNP.Outside.L_pcx_231_aux.Assemble

namespace PEqualNP.Outside.L_pcx_231_aux.Bounds

open scoped BigOperators

abbrev Word (n : Nat) := Fin n → Bool

def Near {n} (a b : Word n) := (Finset.univ.filter fun k => a k ≠ b k).card ≤ 1

def covers {n} (S : Finset (Word n)) := ∀ x, ∃ c ∈ S, Near x c

private theorem card_word (n : Nat) : Fintype.card (Word n) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private def setBit {n : Nat} (x : Word n) (i : Fin n) (b : Bool) : Word n :=
  fun k => if k = i then b else x k

private theorem near_setBit {n : Nat} (x : Word n) (i : Fin n) (b : Bool) :
    Near x (setBit x i b) := by
  unfold Near
  have hs : (Finset.univ.filter fun k => x k ≠ setBit x i b k) ⊆
      ({i} : Finset (Fin n)) := by
    intro k hk
    apply Finset.mem_singleton.mpr
    by_contra hki
    exact (Finset.mem_filter.mp hk).2 (by simp [setBit, hki])
  simpa only [Finset.card_singleton] using Finset.card_le_card hs

private def flip {n : Nat} (x : Word n) : Option (Fin n) → Word n
  | none => x
  | some i => setBit x i (Bool.not (x i))

private theorem flip_flip {n : Nat} (x : Word n) (j : Option (Fin n)) :
    flip (flip x j) j = x := by
  cases j with
  | none => rfl
  | some i =>
    funext k
    by_cases hk : k = i
    · subst k
      simp [flip, setBit]
    · simp [flip, setBit, hk]

private theorem near_flip {n : Nat} (x : Word n) (j : Option (Fin n)) :
    Near x (flip x j) := by
  cases j with
  | none => simp [Near, flip]
  | some i => exact near_setBit x i (Bool.not (x i))

private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = Bool.not b := by
  cases a <;> cases b <;> simp_all

private theorem eq_flip_of_near {n : Nat} {x c : Word n} (h : Near x c) :
    ∃ j : Option (Fin n), x = flip c j := by
  classical
  by_cases hxc : x = c
  · exact ⟨none, hxc⟩
  have hex : ∃ i, x i ≠ c i := by
    by_contra hn
    apply hxc
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  unfold Near at h
  have hi_mem : i ∈ Finset.univ.filter (fun j => x j ≠ c j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  refine ⟨some i, ?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simpa [flip, setBit] using bool_eq_not_of_ne hi
  · have he : x k = c k := by
      by_contra hn
      have hk_mem : k ∈ Finset.univ.filter (fun j => x j ≠ c j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      exact hki (Finset.card_le_one.mp h k hk_mem i hi_mem)
    simpa [flip, setBit, hki] using he

theorem sphere_covering_bound {n : Nat} {S : Finset (Word n)} (hS : covers S) :
    2 ^ n ≤ (n + 1) * S.card := by
  classical
  let ball (c : Word n) : Finset (Word n) :=
    (Finset.univ : Finset (Option (Fin n))).image (flip c)
  have hball (c : Word n) : (ball c).card ≤ n + 1 := by
    simpa only [Fintype.card_option, Fintype.card_fin] using
      (show (ball c).card ≤ Fintype.card (Option (Fin n)) from Finset.card_image_le)
  have hall : (Finset.univ : Finset (Word n)) ⊆ S.biUnion ball := by
    intro x _
    obtain ⟨c, hc, hx⟩ := hS x
    obtain ⟨j, hj⟩ := eq_flip_of_near hx
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩⟩
  calc
    2 ^ n = (Finset.univ : Finset (Word n)).card := (card_word n).symm
    _ ≤ (S.biUnion ball).card := Finset.card_le_card hall
    _ ≤ ∑ c ∈ S, (ball c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ S, (n + 1) := Finset.sum_le_sum fun c _ => hball c
    _ = (n + 1) * S.card := by rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem quarter_cover {n : Nat} (hn : 3 ≤ n) :
    ∃ T : Finset (Word n), covers T ∧ 4 * T.card ≤ 2 ^ n := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := fun h => (by decide : (0 : Nat) ≠ 1) (congrArg Fin.val h)
  have hik : i ≠ k := fun h => (by decide : (0 : Nat) ≠ 2) (congrArg Fin.val h)
  have hjk : j ≠ k := fun h => (by decide : (1 : Nat) ≠ 2) (congrArg Fin.val h)
  let T : Finset (Word n) := Finset.univ.filter fun x => x i = x j ∧ x i = x k
  have mem_T (x : Word n) : x ∈ T ↔ x i = x j ∧ x i = x k := by simp [T]
  refine ⟨T, ?_, ?_⟩
  · intro x
    by_cases h₁ : x i = x j
    · refine ⟨setBit x k (x i), (mem_T _).mpr ?_, near_setBit x k (x i)⟩
      simp [setBit, hik, hjk, h₁]
    · by_cases h₂ : x i = x k
      · refine ⟨setBit x j (x i), (mem_T _).mpr ?_, near_setBit x j (x i)⟩
        simp [setBit, hij, hjk.symm, h₂]
      · have h₃ : x j = x k :=
          (bool_eq_not_of_ne (Ne.symm h₁)).trans (bool_eq_not_of_ne (Ne.symm h₂)).symm
        refine ⟨setBit x i (x j), (mem_T _).mpr ?_, near_setBit x i (x j)⟩
        simp [setBit, hij.symm, hik.symm, h₃]
  · let encode : (↥T × Bool × Bool) → Word n := fun z t =>
      if t = j then z.2.1 else if t = k then z.2.2 else z.1.val t
    have hinj : Function.Injective encode := by
      intro u v huv
      have hu := (mem_T u.1.val).mp u.1.property
      have hv := (mem_T v.1.val).mp v.1.property
      have hi : u.1.val i = v.1.val i := by
        simpa [encode, hij, hik] using congrFun huv i
      have hcenter : u.1 = v.1 := by
        apply Subtype.ext
        funext t
        by_cases htj : t = j
        · subst t
          exact hu.1.symm.trans (hi.trans hv.1)
        · by_cases htk : t = k
          · subst t
            exact hu.2.symm.trans (hi.trans hv.2)
          · simpa [encode, htj, htk] using congrFun huv t
      refine Prod.ext hcenter (Prod.ext ?_ ?_)
      · simpa [encode] using congrFun huv j
      · simpa [encode, hjk.symm] using congrFun huv k
    calc
      4 * T.card = Fintype.card (↥T × Bool × Bool) := by
        simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool] using
          Nat.mul_comm 4 T.card
      _ ≤ Fintype.card (Word n) := Fintype.card_le_of_injective encode hinj
      _ = 2 ^ n := card_word n

private abbrev Syndrome (r : Nat) := Fin r → ZMod 2

private theorem vec_add_self {r : Nat} (v : Syndrome r) : v + v = 0 := by
  funext t
  exact CharTwo.add_self_eq_zero (v t)

private def syndrome {n r : Nat} (label : Option (Fin n) ≃ Syndrome r) (x : Word n) :
    Syndrome r :=
  ∑ k : Fin n, if x k then label (some k) else 0

private theorem syndrome_flip {n r : Nat} (label : Option (Fin n) ≃ Syndrome r)
    (h₀ : label none = 0) (x : Word n) (j : Option (Fin n)) :
    syndrome label (flip x j) = syndrome label x + label j := by
  cases j with
  | none => simp [flip, h₀]
  | some i =>
    have point (k : Fin n) :
        (if flip x (some i) k then label (some k) else 0) =
        (if x k then label (some k) else 0) + (if k = i then label (some i) else 0) := by
      by_cases hki : k = i
      · subst k
        cases hi : x i <;> simp [flip, setBit, hi, vec_add_self]
      · simp [flip, setBit, hki]
    have hsum : (∑ k : Fin n, if k = i then label (some i) else 0) = label (some i) := by
      calc
        _ = (if i = i then label (some i) else 0) := by
          apply Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
          intro k _ hki
          simp [hki]
        _ = _ := if_pos rfl
    calc
      syndrome label (flip x (some i)) = ∑ k : Fin n,
          ((if x k then label (some k) else 0) + (if k = i then label (some i) else 0)) :=
        Finset.sum_congr rfl (fun k _ => point k)
      _ = syndrome label x + label (some i) := by
        simp only [Finset.sum_add_distrib, hsum, syndrome]

theorem perfect_cover {n r : Nat} (h : n + 1 = 2 ^ r) :
    ∃ T : Finset (Word n), covers T ∧ (n + 1) * T.card = 2 ^ n := by
  classical
  let label₀ : Option (Fin n) ≃ Syndrome r := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_option, Fintype.card_fin, Fintype.card_fun, ZMod.card] using h)
  let label : Option (Fin n) ≃ Syndrome r := label₀.trans (Equiv.swap (label₀ none) 0)
  have h₀ : label none = 0 := Equiv.swap_apply_left _ _
  let T : Finset (Word n) := Finset.univ.filter fun x => syndrome label x = 0
  have mem_T (x : Word n) : x ∈ T ↔ syndrome label x = 0 := by simp [T]
  let pick (x : Word n) : Option (Fin n) := label.symm (syndrome label x)
  have hpick (x : Word n) : label (pick x) = syndrome label x := label.apply_symm_apply _
  have hcorrect (x : Word n) : flip x (pick x) ∈ T := by
    apply (mem_T _).mpr
    rw [syndrome_flip label h₀, hpick, vec_add_self]
  let e : Word n ≃ (↥T × Option (Fin n)) :=
    { toFun := fun x => (⟨flip x (pick x), hcorrect x⟩, pick x)
      invFun := fun p => flip p.1.val p.2
      left_inv := fun x => flip_flip x (pick x)
      right_inv := by
        rintro ⟨c, j⟩
        have hp : pick (flip c.val j) = j := by
          apply label.injective
          rw [hpick, syndrome_flip label h₀, (mem_T _).mp c.property, zero_add]
        apply Prod.ext
        · apply Subtype.ext
          change flip (flip c.val j) (pick (flip c.val j)) = c.val
          rw [hp, flip_flip]
        · exact hp }
  refine ⟨T, ?_, ?_⟩
  · intro x
    exact ⟨flip x (pick x), hcorrect x, near_flip x (pick x)⟩
  · calc
      (n + 1) * T.card = Fintype.card (↥T × Option (Fin n)) := by
        simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_option,
          Fintype.card_fin] using Nat.mul_comm (n + 1) T.card
      _ = Fintype.card (Word n) := (Fintype.card_congr e).symm
      _ = 2 ^ n := card_word n

end PEqualNP.Outside.L_pcx_231_aux.Bounds

namespace PEqualNP.Outside.L_pcx_231_aux.Pins

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Pat (n : ℕ) := Fin (n - 1) → Bool
abbrev Row (n : ℕ) := Fin n × Pat n
abbrev V (n : ℕ) := Sum (Fin n) (Row n)
abbrev Pin (n : ℕ) := PEqualNP.ProofComplexity.Literal (V n)

def coordinate (n : ℕ) (hn : 0 < n) (i : Fin n) (j : Fin (n - 1)) : Fin n :=
  ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

def window (n : ℕ) (hn : 0 < n) (i : Fin n) (x : Word n) : Pat n :=
  fun j => x (coordinate n hn i j)

def fiberEquiv (n : ℕ) (hn : 0 < n) (i : Fin n) (x y : Word n) : Prop :=
  window n hn i x = window n hn i y

theorem fiberEquiv_equivalence (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Equivalence (fiberEquiv n hn i) := by
  constructor
  · intro x
    rfl
  · intro x y h
    exact Eq.symm h
  · intro x y z hxy hyz
    exact Eq.trans hxy hyz

def label {n : ℕ} (r : Row n) : Pin n := (Sum.inr r, false)

def labelEmbedding (n : ℕ) : Row n ↪ Pin n where
  toFun := label
  inj' := by
    intro r s h
    exact Sum.inr.inj (congrArg Prod.fst h)

def negativePins (n : ℕ) (A : Finset (Row n)) : Finset (Pin n) :=
  A.map (labelEmbedding n)

theorem mem_negativePins {n : ℕ} {A : Finset (Row n)} {e : Pin n} :
    e ∈ negativePins n A ↔ ∃ r ∈ A, label r = e :=
  Finset.mem_map

@[simp] theorem card_negativePins (n : ℕ) (A : Finset (Row n)) :
    (negativePins n A).card = A.card :=
  Finset.card_map _

private def rawWord {n : ℕ} (a : V n → Bool) : Word n := fun k => a (Sum.inl k)

def accepts (n : ℕ) (hn : 0 < n) (a : V n → Bool) : Prop :=
  ∀ i : Fin n, a (Sum.inr (i, window n hn i (rawWord a))) = true

def fits {n : ℕ} (Q : Finset (Pin n)) (a : V n → Bool) : Prop :=
  ∀ e ∈ Q, a e.1 = e.2

def core (n : ℕ) (hn : 0 < n) (Q : Finset (Pin n)) : Prop :=
  (∃ a, fits Q a) ∧ (¬ ∃ a, accepts n hn a ∧ fits Q a) ∧
    ∀ e ∈ Q, ∃ a, accepts n hn a ∧ fits (Q.erase e) a

def hits (n : ℕ) (hn : 0 < n) (A : Finset (Row n)) : Prop :=
  ∀ x : Word n, ∃ r ∈ A, window n hn r.1 x = r.2

def minimal (n : ℕ) (hn : 0 < n) (A : Finset (Row n)) : Prop :=
  hits n hn A ∧ ∀ r ∈ A, ¬ hits n hn (A.erase r)

private theorem accepts_row {n : ℕ} {hn : 0 < n} {a : V n → Bool}
    (ha : accepts n hn a) {r : Row n} (hr : window n hn r.1 (rawWord a) = r.2) :
    a (Sum.inr r) = true := by
  change a (Sum.inr (r.1, r.2)) = true
  rw [← hr]
  exact ha r.1

theorem core_negativePins_of_minimal (n : ℕ) (hn : 0 < n) (A : Finset (Row n))
    (hA : minimal n hn A) : core n hn (negativePins n A) ∧ (negativePins n A).card = A.card := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, card_negativePins n A⟩
  · exact ⟨fun _ => false, fun e he => by
      obtain ⟨r, _, rfl⟩ := mem_negativePins.mp he
      rfl⟩
  · rintro ⟨a, ha, hf⟩
    obtain ⟨r, hr, hmatch⟩ := hA.1 (rawWord a)
    have hfalse : a (Sum.inr r) = false :=
      hf (label r) (mem_negativePins.mpr ⟨r, hr, rfl⟩)
    exact Bool.noConfusion (hfalse.symm.trans (accepts_row ha hmatch))
  · intro e he
    obtain ⟨r, hr, rfl⟩ := mem_negativePins.mp he
    have hmiss := hA.2 r hr
    unfold hits at hmiss
    push Not at hmiss
    obtain ⟨x, hx⟩ := hmiss

    let a : V n → Bool := Sum.elim x (fun s => if s ∈ A.erase r then false else true)
    refine ⟨a, ?_, ?_⟩
    · intro i
      change (if (i, window n hn i x) ∈ A.erase r then false else true) = true
      exact if_neg (fun hs => hx (i, window n hn i x) hs rfl)
    · intro d hd
      obtain ⟨s, hs, rfl⟩ := mem_negativePins.mp (Finset.mem_erase.mp hd).2
      have hsr : s ≠ r := fun h => (Finset.mem_erase.mp hd).1 (congrArg label h)
      change (if s ∈ A.erase r then false else true) = false
      exact if_pos (Finset.mem_erase.mpr ⟨hsr, hs⟩)

theorem exists_minimal_subcover (n : ℕ) (hn : 0 < n) (B : Finset (Row n))
    (hB : hits n hn B) : ∃ A ⊆ B, minimal n hn A := by
  classical
  refine (B.strongInductionOn
    (p := fun S => hits n hn S → ∃ A ⊆ S, minimal n hn A) ?_) hB
  intro S ih hS
  by_cases h : ∀ r ∈ S, ¬ hits n hn (S.erase r)
  · refine ⟨S, ?_, hS, h⟩
    intro r hr
    exact hr
  · push Not at h
    obtain ⟨r, hr, herase⟩ := h
    obtain ⟨A, hA, hmin⟩ := ih (S.erase r) (Finset.erase_ssubset hr) herase
    refine ⟨A, ?_, hmin⟩
    intro s hs
    exact Finset.erase_subset r S (hA hs)

private def replacement {n : ℕ} (i : Fin n → Fin n) (j : Fin n → Fin (n - 1)) :
    Pin n → Row n → Prop
  | (Sum.inl k, b), r => r.1 = i k ∧ r.2 (j k) ≠ b
  | (Sum.inr s, b), r => r = s ∧ b = false

private theorem replacement_violated {n : ℕ} {hn : 0 < n}
    {i : Fin n → Fin n} {j : Fin n → Fin (n - 1)}
    (hij : ∀ k, coordinate n hn (i k) (j k) = k)
    {a : V n → Bool} (ha : accepts n hn a) {e : Pin n} {r : Row n}
    (he : replacement i j e r) (hr : window n hn r.1 (rawWord a) = r.2) :
    a e.1 ≠ e.2 := by
  rcases e with ⟨k | s, b⟩
  · change r.1 = i k ∧ r.2 (j k) ≠ b at he
    have hentry := congrFun hr (j k)
    rw [he.1] at hentry
    change rawWord a (coordinate n hn (i k) (j k)) = r.2 (j k) at hentry
    rw [hij k] at hentry
    change rawWord a k ≠ b
    exact fun h => he.2 (hentry.symm.trans h)
  · change r = s ∧ b = false at he
    change a (Sum.inr s) ≠ b
    rw [← he.1, he.2]
    exact fun h => Bool.noConfusion ((accepts_row ha hr).symm.trans h)

theorem replacement_cover_of_core (n : ℕ) (hn : 0 < n)
    (hcoord : ∀ k : Fin n, ∃ (i : Fin n) (j : Fin (n - 1)), (i.val + j.val) % n = k.val)
    (Q : Finset (Pin n)) (hQ : core n hn Q) :
    ∃ B : Finset (Row n), hits n hn B ∧ (∀ r : Row n, (Sum.inr r, true) ∉ Q) ∧
      ∀ A ⊆ B, hits n hn A → Q.card ≤ A.card := by
  classical
  choose i j hmod using hcoord
  have hij (k : Fin n) : coordinate n hn (i k) (j k) = k := Fin.ext (hmod k)
  obtain ⟨⟨a₀, ha₀⟩, hbad, hprivate⟩ := hQ
  let B : Finset (Row n) := Finset.univ.filter (fun r => ∃ e ∈ Q, replacement i j e r)
  have memB (r : Row n) : r ∈ B ↔ ∃ e ∈ Q, replacement i j e r := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  have hB : hits n hn B := by
    intro x
    by_contra hx

    let a : V n → Bool := Sum.elim x (fun r =>
      if window n hn r.1 x = r.2 then true else a₀ (Sum.inr r))
    apply hbad
    refine ⟨a, ?_, ?_⟩
    · intro k
      change (if window n hn k x = window n hn k x then true
        else a₀ (Sum.inr (k, window n hn k x))) = true
      exact if_pos rfl
    · intro e he
      rcases e with ⟨k | r, b⟩
      · change x k = b
        by_cases hkb : x k = b
        · exact hkb
        · let r' : Row n := (i k, window n hn (i k) x)
          have hr' : replacement i j (Sum.inl k, b) r' := by
            change i k = i k ∧ x (coordinate n hn (i k) (j k)) ≠ b
            rw [hij k]
            exact ⟨rfl, hkb⟩
          exact (hx ⟨r', (memB r').2 ⟨_, he, hr'⟩, rfl⟩).elim
      · change (if window n hn r.1 x = r.2 then true else a₀ (Sum.inr r)) = b
        by_cases hr : window n hn r.1 x = r.2
        · rw [if_pos hr]
          cases b with
          | false =>
            have hrep : replacement i j (Sum.inr r, false) r := ⟨rfl, rfl⟩
            exact (hx ⟨r, (memB r).2 ⟨_, he, hrep⟩, hr⟩).elim
          | true => rfl
        · rw [if_neg hr]
          exact ha₀ (Sum.inr r, b) he

  have only_private {e d : Pin n} {a : V n → Bool} {r : Row n}
      (ha : accepts n hn a) (hf : fits (Q.erase e) a)
      (hr : window n hn r.1 (rawWord a) = r.2)
      (hd : d ∈ Q) (hrep : replacement i j d r) : d = e := by
    by_contra hne
    exact replacement_violated hij ha hrep hr (hf d (Finset.mem_erase.mpr ⟨hne, hd⟩))
  have private_row {e : Pin n} {a : V n → Bool} {r : Row n}
      (ha : accepts n hn a) (hf : fits (Q.erase e) a)
      (hr : window n hn r.1 (rawWord a) = r.2) (hrow : r ∈ B) : replacement i j e r := by
    obtain ⟨d, hd, hrep⟩ := (memB r).1 hrow
    have hde := only_private ha hf hr hd hrep
    simpa only [hde] using hrep
  refine ⟨B, hB, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, ha, hf⟩ := hprivate (Sum.inr r, true) hr
    obtain ⟨s, hs, hmatch⟩ := hB (rawWord a)
    have hrep := private_row ha hf hmatch hs
    change s = r ∧ true = false at hrep
    exact Bool.noConfusion hrep.2
  · intro A hAB hA
    have hselect (e : Q) : ∃ a, accepts n hn a ∧ fits (Q.erase e.val) a :=
      hprivate e.val e.property
    choose a ha hf using hselect
    have hex (e : Q) : ∃ r ∈ A, window n hn r.1 (rawWord (a e)) = r.2 :=
      hA (rawWord (a e))
    choose f hfa hmatch using hex
    have hrep (e : Q) : replacement i j e.val (f e) :=
      private_row (ha e) (hf e) (hmatch e) (hAB (hfa e))
    let g : Q → A := fun e => ⟨f e, hfa e⟩
    apply Finset.card_le_card_of_injective (f := g)
    intro e d hed
    have hfd : f e = f d := congrArg Subtype.val hed
    have hdrep : replacement i j d.val (f e) := by
      rw [hfd]
      exact hrep d
    exact Subtype.ext (only_private (ha e) (hf e) (hmatch e) d.property hdrep).symm

theorem minimal_of_core_of_coordinate (n : ℕ) (hn : 0 < n)
    (hcoord : ∀ k : Fin n, ∃ (i : Fin n) (j : Fin (n - 1)), (i.val + j.val) % n = k.val)
    (Q : Finset (Pin n)) (hQ : core n hn Q) :
    ∃ A : Finset (Row n), minimal n hn A ∧ Q.card ≤ A.card := by
  obtain ⟨B, hB, _, hcard⟩ := replacement_cover_of_core n hn hcoord Q hQ
  obtain ⟨A, hAB, hA⟩ := exists_minimal_subcover n hn B hB
  exact ⟨A, hA, hcard A hAB hA.1⟩

theorem minimal_of_core (n : ℕ) (hn : 0 < n) (hn₂ : 2 ≤ n)
    (Q : Finset (Pin n)) (hQ : core n hn Q) :
    ∃ A : Finset (Row n), minimal n hn A ∧ Q.card ≤ A.card := by
  refine minimal_of_core_of_coordinate n hn ?_ Q hQ
  intro k
  refine ⟨k, ⟨0, by omega⟩, ?_⟩
  change (k.val + 0) % n = k.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt k.isLt]

end PEqualNP.Outside.L_pcx_231_aux.Pins

theorem PEqualNP.Outside.L_pcx_231 : (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
  let Word := Fin n → Bool
  let Pat := Fin (n - 1) → Bool
  let V := Sum (Fin n) (Fin n × Pat)
  let Pin := PEqualNP.ProofComplexity.Literal V
  let accepts := fun (a : V → Bool) =>
    ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (n - 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true
  let fits := fun (pins : Finset Pin) (a : V → Bool) => ∀ l ∈ pins, a l.1 = l.2
  let core := fun (candidate : Finset Pin) =>
    (∃ a, fits candidate a) ∧ (¬ ∃ a, accepts a ∧ fits candidate a) ∧
    ∀ e ∈ candidate, ∃ a, accepts a ∧ fits (candidate.erase e) a
  let covers := fun (centers : Finset Word) =>
    ∀ x : Word, ∃ c ∈ centers, (Finset.univ.filter (fun k : Fin n => x k ≠ c k)).card ≤ 1
  ∃ (P : Finset Pin) (S : Finset Word),
    core P ∧ (∀ l ∈ P, ∃ i : Fin n, ∃ p : Pat, l = (Sum.inr (i, p), false)) ∧
    (∀ Q, core Q → Q.card ≤ P.card) ∧ covers S ∧
    (∀ T, covers T → S.card ≤ T.card) ∧ P.card + S.card = 2 ^ n ∧
    (3 ≤ n → 3 * 2 ^ n ≤ 4 * P.card) ∧
    ((∃ r : ℕ, n + 1 = 2 ^ r) → (n + 1) * P.card = n * 2 ^ n)) := by
  intro n hn hn₂
  dsimp only
  classical
  refine PEqualNP.Outside.L_pcx_231_aux.Assemble.finish hn (PEqualNP.Outside.L_pcx_231_aux.Pins.core n hn)
    (fun (l : PEqualNP.Outside.L_pcx_231_aux.Pins.Pin n) =>
      ∃ i : Fin n, ∃ p : PEqualNP.Outside.L_pcx_231_aux.Pins.Pat n, l = (Sum.inr (i, p), false))
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hcore, hcard⟩ := PEqualNP.Outside.L_pcx_231_aux.Pins.core_negativePins_of_minimal n hn A hA
    refine ⟨PEqualNP.Outside.L_pcx_231_aux.Pins.negativePins n A, hcore, ?_, hcard⟩
    intro l hl
    obtain ⟨⟨i, p⟩, _, he⟩ := PEqualNP.Outside.L_pcx_231_aux.Pins.mem_negativePins.mp hl
    exact ⟨i, p, he.symm⟩
  · exact PEqualNP.Outside.L_pcx_231_aux.Pins.minimal_of_core n hn hn₂
  · intro S hs
    exact PEqualNP.Outside.L_pcx_231_aux.Bounds.sphere_covering_bound hs
  · exact PEqualNP.Outside.L_pcx_231_aux.Bounds.quarter_cover
  · intro r hr
    exact PEqualNP.Outside.L_pcx_231_aux.Bounds.perfect_cover hr
