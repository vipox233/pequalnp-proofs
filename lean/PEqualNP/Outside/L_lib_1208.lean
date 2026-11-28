import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_lib_1208

-- Part A: derivations as lists of functions

def Av {X : Type} (B : Set (X → Bool)) (L : List (X → Bool)) (f : X → Bool) : Prop :=
  ∃ g, (g ∈ B ∨ g ∈ L ∨ g = fun _ => true) ∧ (f = g ∨ f = fun x => !(g x))

def Valid {X : Type} (B : Set (X → Bool)) : List (X → Bool) → Prop
  | [] => True
  | g :: L => Valid B L ∧ ∃ u, Av B L u ∧ ∃ v, Av B L v ∧
      (g = (fun x => u x && v x) ∨ g = (fun x => u x || v x))

theorem valid_nil {X : Type} (B : Set (X → Bool)) : Valid B [] := True.intro

theorem valid_cons {X : Type} (B : Set (X → Bool)) (g : X → Bool) (L : List (X → Bool)) :
    Valid B (g :: L) ↔ (Valid B L ∧ ∃ u, Av B L u ∧ ∃ v, Av B L v ∧
      (g = (fun x => u x && v x) ∨ g = (fun x => u x || v x))) := Iff.rfl

theorem av_iff {X : Type} (B : Set (X → Bool)) (L : List (X → Bool)) (f : X → Bool) :
    Av B L f ↔ ∃ g, (g ∈ B ∨ g ∈ L ∨ g = fun _ => true) ∧ (f = g ∨ f = fun x => !(g x)) := Iff.rfl

theorem av_gen {X : Type} {B : Set (X → Bool)} {L : List (X → Bool)} {g : X → Bool}
    (hg : g ∈ B ∨ g ∈ L ∨ g = fun _ => true) : Av B L g :=
  (av_iff B L g).mpr ⟨g, hg, Or.inl rfl⟩

theorem av_not {X : Type} {B : Set (X → Bool)} {L : List (X → Bool)} {f : X → Bool}
    (hf : Av B L f) : Av B L (fun x => !(f x)) := by
  obtain ⟨g, hg, hfg | hfg⟩ := hf
  · exact (av_iff B L _).mpr ⟨g, hg, Or.inr (by rw [hfg])⟩
  · refine (av_iff B L _).mpr ⟨g, hg, Or.inl ?_⟩
    rw [hfg]
    funext x
    simp

theorem av_true {X : Type} {B : Set (X → Bool)} {L : List (X → Bool)} :
    Av B L (fun _ => true) := av_gen (Or.inr (Or.inr rfl))

theorem av_false {X : Type} {B : Set (X → Bool)} {L : List (X → Bool)} :
    Av B L (fun _ => false) := av_not (av_true (B := B) (L := L))

theorem av_ind {X : Type} (B : Set (X → Bool)) (L : List (X → Bool)) (Pr : (X → Bool) → Prop)
    (hgen : ∀ g, (g ∈ B ∨ g ∈ L ∨ g = fun _ => true) → Pr g)
    (hnot : ∀ g, Pr g → Pr (fun x => !(g x))) : ∀ f, Av B L f → Pr f := by
  intro f hf
  obtain ⟨g, hg, hfg | hfg⟩ := hf
  · rw [hfg]; exact hgen g hg
  · rw [hfg]; exact hnot g (hgen g hg)

theorem av_mono {X : Type} {B : Set (X → Bool)} {L : List (X → Bool)} (g : X → Bool) {f : X → Bool}
    (hf : Av B L f) : Av B (g :: L) f := by
  obtain ⟨gp, hg, hfg⟩ := hf
  refine (av_iff _ _ _).mpr ⟨gp, ?_, hfg⟩
  rcases hg with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
  · exact Or.inr (Or.inr h)

theorem av_cons_cases {X : Type} {B : Set (X → Bool)} {L : List (X → Bool)} {g f : X → Bool}
    (hf : Av B (g :: L) f) : Av B L f ∨ (f = g ∨ f = fun x => !(g x)) := by
  obtain ⟨gp, hg, hfg⟩ := hf
  rcases hg with h | h | h
  · exact Or.inl ((av_iff _ _ _).mpr ⟨gp, Or.inl h, hfg⟩)
  · rcases List.mem_cons.mp h with h | h
    · rw [h] at hfg; exact Or.inr hfg
    · exact Or.inl ((av_iff _ _ _).mpr ⟨gp, Or.inr (Or.inl h), hfg⟩)
  · exact Or.inl ((av_iff _ _ _).mpr ⟨gp, Or.inr (Or.inr h), hfg⟩)

theorem pin_step {X : Type} (ρ : X → X) (B Bp : Set (X → Bool)) (bz : X → Bool)
    (hB : ∀ b, b ∈ B → b = bz ∨ ((fun x => b (ρ x)) = b ∧ b ∈ Bp))
    (hz : ∀ x, bz (ρ x) = true) :
    ∀ L : List (X → Bool), Valid B L →
      ∃ Lp : List (X → Bool), Valid Bp Lp ∧
        (∀ f, Av B L f → Av Bp Lp (fun x => f (ρ x))) ∧
        (Lp.length + 1 ≤ L.length ∨ (Lp.length ≤ L.length ∧
          ∀ f, Av B L f → (f = bz ∨ f = (fun x => !(bz x)) ∨ (fun x => f (ρ x)) = f))) := by
  have hnotP : ∀ g : X → Bool, (g = bz ∨ g = (fun x => !(bz x)) ∨ (fun x => g (ρ x)) = g) →
      ((fun x => !(g x)) = bz ∨ (fun x => !(g x)) = (fun x => !(bz x)) ∨
        (fun x => (fun y => !(g y)) (ρ x)) = (fun x => !(g x))) := by
    intro g hg
    rcases hg with h | h | h
    · exact Or.inr (Or.inl (by rw [h]))
    · left; rw [h]; funext x; simp
    · right; right; funext x
      have e : g (ρ x) = g x := congrFun h x
      show (!(g (ρ x))) = !(g x)
      rw [e]
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨[], valid_nil Bp, ?_, Or.inr ⟨le_refl _, ?_⟩⟩
    · refine av_ind B [] (fun f => Av Bp [] (fun x => f (ρ x))) ?_ ?_
      · intro g hg
        show Av Bp [] (fun x => g (ρ x))
        rcases hg with h | h | h
        · rcases hB g h with hb | ⟨e, hbp⟩
          · have ht : (fun x => g (ρ x)) = fun _ => true := by rw [hb]; exact funext hz
            rw [ht]; exact av_true
          · rw [e]; exact av_gen (Or.inl hbp)
        · cases h
        · rw [h]; exact av_true
      · intro g hg; exact av_not hg
    · refine av_ind B [] (fun f => f = bz ∨ f = (fun x => !(bz x)) ∨ (fun x => f (ρ x)) = f) ?_ hnotP
      intro g hg
      rcases hg with h | h | h
      · rcases hB g h with hb | ⟨e, _⟩
        · exact Or.inl hb
        · exact Or.inr (Or.inr e)
      · cases h
      · rw [h]; exact Or.inr (Or.inr rfl)
  | cons g Lz ih =>
    intro hV
    obtain ⟨hVz, u, hu, v, hv, hg⟩ := (valid_cons B g Lz).mp hV
    obtain ⟨Lq, hVq, havq, hlen⟩ := ih hVz
    have hup := havq u hu
    have hvp := havq v hv
    have htr : ∀ Lr : List (X → Bool), (∀ f, Av B Lz f → Av Bp Lr (fun x => f (ρ x))) →
        Av Bp Lr (fun x => g (ρ x)) → ∀ f, Av B (g :: Lz) f → Av Bp Lr (fun x => f (ρ x)) := by
      intro Lr hone htwo
      refine av_ind B (g :: Lz) (fun f => Av Bp Lr (fun x => f (ρ x))) ?_ ?_
      · intro gp hgp
        show Av Bp Lr (fun x => gp (ρ x))
        rcases hgp with h | h | h
        · exact hone gp (av_gen (Or.inl h))
        · rcases List.mem_cons.mp h with h | h
          · rw [h]; exact htwo
          · exact hone gp (av_gen (Or.inr (Or.inl h)))
        · exact hone gp (av_gen (Or.inr (Or.inr h)))
      · intro gp hgp; exact av_not hgp
    have hvalid : Valid Bp ((fun x => g (ρ x)) :: Lq) := by
      refine (valid_cons _ _ _).mpr ⟨hVq, (fun x => u (ρ x)), hup, (fun x => v (ρ x)), hvp, ?_⟩
      rcases hg with h | h
      · left; rw [h]
      · right; rw [h]
    have hkeep : ∀ f, Av B (g :: Lz) f → Av Bp ((fun x => g (ρ x)) :: Lq) (fun x => f (ρ x)) :=
      htr _ (fun f hf => av_mono _ (havq f hf))
        (av_gen (Or.inr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))))
    have hkill : ∀ (s t : X → Bool), Av Bp Lq (fun x => t (ρ x)) →
        (s = bz ∨ s = fun x => !(bz x)) →
        (g = (fun x => s x && t x) ∨ g = (fun x => s x || t x) ∨
          g = (fun x => t x && s x) ∨ g = (fun x => t x || s x)) →
        Av Bp Lq (fun x => g (ρ x)) := by
      intro s t ht hs hgs
      rcases hs with hs | hs <;> rcases hgs with hgs | hgs | hgs | hgs <;> rw [hgs, hs] <;>
        simp only [hz, Bool.not_true, Bool.true_and, Bool.true_or, Bool.and_true, Bool.or_true,
          Bool.false_and, Bool.false_or, Bool.and_false, Bool.or_false] <;>
        first | exact ht | exact av_true | exact av_false
    have hstrict : Av Bp Lq (fun x => g (ρ x)) →
        ∃ Lp : List (X → Bool), Valid Bp Lp ∧
        (∀ f, Av B (g :: Lz) f → Av Bp Lp (fun x => f (ρ x))) ∧
        (Lp.length + 1 ≤ (g :: Lz).length ∨ (Lp.length ≤ (g :: Lz).length ∧
          ∀ f, Av B (g :: Lz) f → (f = bz ∨ f = (fun x => !(bz x)) ∨ (fun x => f (ρ x)) = f))) := by
      intro hk
      refine ⟨Lq, hVq, htr Lq havq hk, Or.inl ?_⟩
      rcases hlen with h | ⟨h, _⟩ <;> simp only [List.length_cons] <;> omega
    rcases hlen with hlt | ⟨hle, hD⟩
    · exact ⟨_, hvalid, hkeep, Or.inl (by simp only [List.length_cons]; omega)⟩
    · rcases hD u hu with hub | hub | hub
      · exact hstrict (hkill u v hvp (Or.inl hub) (by
          rcases hg with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)))
      · exact hstrict (hkill u v hvp (Or.inr hub) (by
          rcases hg with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)))
      · rcases hD v hv with hvb | hvb | hvb
        · exact hstrict (hkill v u hup (Or.inl hvb) (by
            rcases hg with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))))
        · exact hstrict (hkill v u hup (Or.inr hvb) (by
            rcases hg with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))))
        · refine ⟨_, hvalid, hkeep, Or.inr ⟨by simp only [List.length_cons]; omega, ?_⟩⟩
          refine av_ind B (g :: Lz)
            (fun f => f = bz ∨ f = (fun x => !(bz x)) ∨ (fun x => f (ρ x)) = f) ?_ hnotP
          intro gp hgp
          rcases hgp with h | h | h
          · exact hD gp (av_gen (Or.inl h))
          · rcases List.mem_cons.mp h with h | h
            · right; right
              rw [h]
              funext x
              have eu : u (ρ x) = u x := congrFun hub x
              have ev : v (ρ x) = v x := congrFun hvb x
              rcases hg with hgg | hgg
              · rw [hgg]
                show (u (ρ x) && v (ρ x)) = (u x && v x)
                rw [eu, ev]
              · rw [hgg]
                show (u (ρ x) || v (ρ x)) = (u x || v x)
                rw [eu, ev]
            · exact hD gp (av_gen (Or.inr (Or.inl h)))
          · exact hD gp (av_gen (Or.inr (Or.inr h)))

-- Part B: the pinning step on graphs

def BS {n : ℕ} (S : Finset (Fin n)) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ i, i ∈ S ∧ f = fun x => x i}

theorem bs_iff {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    f ∈ BS S ↔ ∃ i, i ∈ S ∧ f = fun x => x i := Iff.rfl

def CovS {n : ℕ} (G : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ e ∈ G, e.1 ∈ S → e.2 ∈ S → x e.1 = true ∨ x e.2 = true

def Inv {n : ℕ} (G : Finset (Fin n × Fin n)) (a b c : Fin n) (S : Finset (Fin n))
    (L : List ((Fin n → Bool) → Bool)) : Prop :=
  Valid (BS S) L ∧
  (∃ D, Av (BS S) L D ∧ ∀ x, (D x = true ↔ CovS G S x)) ∧
  (∃ P, Av (BS S) L P ∧ ∀ x, CovS G S x → P x = xor (x a) (x b)) ∧
  (∃ Q, Av (BS S) L Q ∧ ∀ x, CovS G S x → Q x = xor (x b) (x c))

theorem inv_iff {n : ℕ} (G : Finset (Fin n × Fin n)) (a b c : Fin n) (S : Finset (Fin n))
    (L : List ((Fin n → Bool) → Bool)) :
    Inv G a b c S L ↔ (Valid (BS S) L ∧
      (∃ D, Av (BS S) L D ∧ ∀ x, (D x = true ↔ CovS G S x)) ∧
      (∃ P, Av (BS S) L P ∧ ∀ x, CovS G S x → P x = xor (x a) (x b)) ∧
      (∃ Q, Av (BS S) L Q ∧ ∀ x, CovS G S x → Q x = xor (x b) (x c))) := Iff.rfl

theorem upd_ne {n : ℕ} (x : Fin n → Bool) (v i : Fin n) (h : i ≠ v) :
    Function.update x v true i = x i := by
  simp [Function.update, h]

theorem upd_self {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    Function.update x v true v = true := by
  simp

theorem cov_upd {n : ℕ} (G : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) (x : Fin n → Bool) :
    CovS G (insert v S) (Function.update x v true) ↔ CovS G S x := by
  constructor
  · intro h e he hea heb
    have hna : e.1 ≠ v := fun hh => hv (hh ▸ hea)
    have hnb : e.2 ≠ v := fun hh => hv (hh ▸ heb)
    have hh := h e he (Finset.mem_insert_of_mem hea) (Finset.mem_insert_of_mem heb)
    rw [upd_ne x v _ hna, upd_ne x v _ hnb] at hh
    exact hh
  · intro h e he hea heb
    by_cases hna : e.1 = v
    · left; rw [hna]; exact upd_self x v
    · by_cases hnb : e.2 = v
      · right; rw [hnb]; exact upd_self x v
      · rw [upd_ne x v _ hna, upd_ne x v _ hnb]
        exact h e he ((Finset.mem_insert.mp hea).resolve_left hna)
          ((Finset.mem_insert.mp heb).resolve_left hnb)

theorem step {n : ℕ} (G : Finset (Fin n × Fin n)) (hlt : ∀ e ∈ G, e.1 < e.2) (a b c : Fin n)
    (S : Finset (Fin n)) (v u : Fin n) (hv : v ∉ S) (hu : u ∈ S)
    (hadj : (u, v) ∈ G ∨ (v, u) ∈ G) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (habadj : (a, b) ∈ G ∨ (b, a) ∈ G)
    (L : List ((Fin n → Bool) → Bool)) (hI : Inv G a b c (insert v S) L) :
    ∃ Lp, Inv G a b c S Lp ∧ Lp.length + 1 ≤ L.length := by
  obtain ⟨hV, ⟨D, hDav, hD⟩, ⟨P, hPav, hP⟩, ⟨Q, hQav, hQ⟩⟩ := hI
  have hav : a ≠ v := fun hh => hv (hh ▸ ha)
  have hbv : b ≠ v := fun hh => hv (hh ▸ hb)
  have hcv : c ≠ v := fun hh => hv (hh ▸ hc)
  have hB : ∀ f, f ∈ BS (insert v S) → f = (fun x : Fin n → Bool => x v) ∨
      ((fun x => f (Function.update x v true)) = f ∧ f ∈ BS S) := by
    intro f hf
    obtain ⟨i, hi, hfi⟩ := (bs_iff _ _).mp hf
    rcases Finset.mem_insert.mp hi with hiv | hiS
    · left; rw [hfi, hiv]
    · right
      have hne : i ≠ v := fun hh => hv (hh ▸ hiS)
      rw [hfi]
      exact ⟨funext fun x => upd_ne x v i hne, (bs_iff _ _).mpr ⟨i, hiS, rfl⟩⟩
  obtain ⟨Lp, hVp, havp, hlen⟩ := pin_step (fun x : Fin n → Bool => Function.update x v true)
    (BS (insert v S)) (BS S) (fun x => x v) hB (fun x => upd_self x v) L hV
  refine ⟨Lp, (inv_iff _ _ _ _ _ _).mpr ⟨hVp, ⟨_, havp D hDav, fun x => ?_⟩,
    ⟨_, havp P hPav, fun x hx => ?_⟩, ⟨_, havp Q hQav, fun x hx => ?_⟩⟩, ?_⟩
  · exact (hD _).trans (cov_upd G S v hv x)
  · have hh := hP _ ((cov_upd G S v hv x).mpr hx)
    rw [upd_ne x v a hav, upd_ne x v b hbv] at hh
    exact hh
  · have hh := hQ _ ((cov_upd G S v hv x).mpr hx)
    rw [upd_ne x v b hbv, upd_ne x v c hcv] at hh
    exact hh
  · rcases hlen with hlen | ⟨_, hall⟩
    · exact hlen
    · exfalso
      rcases hall D hDav with hd | hd | hd
      · have hz : D (fun i => decide (i = v)) = true := by rw [hd]; simp
        have hcz := (hD _).mp hz
        rcases habadj with he | he
        · have hh := hcz _ he (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb)
          simp [hav, hbv] at hh
        · have hh := hcz _ he (Finset.mem_insert_of_mem hb) (Finset.mem_insert_of_mem ha)
          simp [hav, hbv] at hh
      · have hz : D (fun _ => true) = true := (hD _).mpr (fun e _ _ _ => Or.inl rfl)
        rw [hd] at hz
        simp at hz
      · obtain ⟨y, hy⟩ : ∃ y : Fin n → Bool, y = fun i => decide (i ≠ u ∧ i ≠ v) := ⟨_, rfl⟩
        have hyr : ∀ i, i ≠ u → Function.update y v true i = true := by
          intro i hi
          by_cases hiv : i = v
          · rw [hiv]; exact upd_self _ _
          · rw [upd_ne _ _ _ hiv, hy]; simp [hi, hiv]
        have hcy : CovS G (insert v S) (Function.update y v true) := by
          intro e he _ _
          by_cases heu : e.1 = u
          · right
            apply hyr
            intro hh
            exact absurd (hlt e he) (by rw [heu, hh]; exact lt_irrefl _)
          · left; exact hyr _ heu
        have hDy : D (Function.update y v true) = true := (hD _).mpr hcy
        have hh : D (Function.update y v true) = D y := congrFun hd y
        have hDyy : D y = true := by rw [← hh]; exact hDy
        have hcyy := (hD _).mp hDyy
        rcases hadj with he | he
        · have hk := hcyy _ he (Finset.mem_insert_of_mem hu) (Finset.mem_insert_self _ _)
          rw [hy] at hk
          simp at hk
        · have hk := hcyy _ he (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hu)
          rw [hy] at hk
          simp at hk

theorem crossing {n : ℕ} (r : Fin n → Fin n → Prop) (S : Finset (Fin n)) (x y : Fin n)
    (h : Relation.ReflTransGen r x y) (hx : x ∈ S) :
    y ∉ S → ∃ u v, u ∈ S ∧ v ∉ S ∧ r u v := by
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail bm cm _ hbc ih =>
    intro hy
    by_cases hb : bm ∈ S
    · exact ⟨bm, cm, hb, hy, hbc⟩
    · exact ih hb

theorem grow {n : ℕ} (G : Finset (Fin n × Fin n)) (hlt : ∀ e ∈ G, e.1 < e.2) (a b c : Fin n)
    (hconn : ∀ i j : Fin n,
      Relation.ReflTransGen (fun i j : Fin n => (i, j) ∈ G ∨ (j, i) ∈ G) i j)
    (habadj : (a, b) ∈ G ∨ (b, a) ∈ G) :
    ∀ (m : ℕ) (S : Finset (Fin n)), a ∈ S → b ∈ S → c ∈ S → n - S.card = m →
      (∀ L, Inv G a b c S L → S.card + 1 ≤ L.length) →
      ∀ L, Inv G a b c Finset.univ L → n + 1 ≤ L.length := by
  intro m
  induction m with
  | zero =>
    intro S ha hb hc hm hS L hI
    have hle : S.card ≤ n := by
      have hh := Finset.card_le_univ S
      simpa using hh
    have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by simp; omega)
    rw [hSu] at hS
    have hh := hS L hI
    simpa using hh
  | succ m ih =>
    intro S ha hb hc hm hS
    have hex : ∃ w, w ∉ S := by
      by_contra hne
      have hall : ∀ w, w ∈ S := fun w => by
        by_contra hw
        exact hne ⟨w, hw⟩
      have hSu : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
      rw [hSu] at hm
      simp at hm
    obtain ⟨w, hw⟩ := hex
    obtain ⟨u, v, hu, hv, huv⟩ := crossing _ S b w (hconn b w) hb hw
    have hcard : (insert v S).card = S.card + 1 := by simp [hv]
    apply ih (insert v S) (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb)
      (Finset.mem_insert_of_mem hc) (by omega)
    intro L hI
    obtain ⟨Lp, hIp, hlen⟩ := step G hlt a b c S v u hv hu huv ha hb hc habadj L hI
    have hh := hS Lp hIp
    omega

-- Part C: the three-vertex base case by a table search

def pt {n : ℕ} (a b c : Fin n) (i j k : Bool) : Fin n → Bool :=
  fun v => if v = a then i else if v = b then j else if v = c then k else true

theorem pt_a {n : ℕ} (a b c : Fin n) (i j k : Bool) : pt a b c i j k a = i := by
  simp [pt]

theorem pt_b {n : ℕ} (a b c : Fin n) (i j k : Bool) (hab : a ≠ b) : pt a b c i j k b = j := by
  simp [pt, hab.symm]

theorem pt_c {n : ℕ} (a b c : Fin n) (i j k : Bool) (hac : a ≠ c) (hbc : b ≠ c) :
    pt a b c i j k c = k := by
  simp [pt, hac.symm, hbc.symm]

def tblOf {n : ℕ} (a b c : Fin n) (f : (Fin n → Bool) → Bool) : List Bool :=
  [f (pt a b c false false false), f (pt a b c true false false),
   f (pt a b c false true false), f (pt a b c true true false),
   f (pt a b c false false true), f (pt a b c true false true),
   f (pt a b c false true true), f (pt a b c true true true)]

def tnot (t : List Bool) : List Bool := t.map fun x => !x

def tand (s t : List Bool) : List Bool := List.zipWith (fun x y => x && y) s t

def tor (s t : List Bool) : List Bool := List.zipWith (fun x y => x || y) s t

def tbase : List (List Bool) :=
  [[false, true, false, true, false, true, false, true],
   [false, false, true, true, false, false, true, true],
   [false, false, false, false, true, true, true, true],
   [true, true, true, true, true, true, true, true]]

def tavail (T : List (List Bool)) : List (List Bool) :=
  (T ++ tbase) ++ (T ++ tbase).map tnot

def tD : List Bool := [false, false, true, true, false, true, true, true]

def isP (t : List Bool) : Bool :=
  match t with
  | [_, _, pc, pd, _, pf, pg, ph] => pc && !pd && pf && pg && !ph
  | _ => false

def isQ (t : List Bool) : Bool :=
  match t with
  | [_, _, pc, pd, _, pf, pg, ph] => pc && pd && pf && !pg && !ph
  | _ => false

def hasD (A : List (List Bool)) : Bool := A.any fun t => t == tD

def hasP (A : List (List Bool)) : Bool := A.any isP

def hasQ (A : List (List Bool)) : Bool := A.any isQ

def IsOp (A : List (List Bool)) (t : List Bool) : Prop :=
  ∃ u, u ∈ A ∧ ∃ v, v ∈ A ∧ (t = tand u v ∨ t = tor u v)

theorem isop_iff (A : List (List Bool)) (t : List Bool) :
    IsOp A t ↔ ∃ u, u ∈ A ∧ ∃ v, v ∈ A ∧ (t = tand u v ∨ t = tor u v) := Iff.rfl

def forOps (A : List (List Bool)) (k : List Bool → Bool) : Bool :=
  A.all fun u => A.all fun v => k (tand u v) && k (tor u v)

theorem forOps_spec (A : List (List Bool)) (k : List Bool → Bool) (h : forOps A k = true)
    (t : List Bool) (ht : IsOp A t) : k t = true := by
  obtain ⟨u, hu, v, hv, htt⟩ := ht
  simp only [forOps, List.all_eq_true, Bool.and_eq_true] at h
  rcases htt with htt | htt
  · rw [htt]; exact (h u hu v hv).1
  · rw [htt]; exact (h u hu v hv).2

def chkTwo (ca cb cc : List (List Bool) → Bool) (tx ty : List Bool) : Bool :=
  !(ca (tavail [ty, tx]) && cb (tavail [ty, tx])) ||
    forOps (tavail [ty, tx]) (fun tz => !(cc (tavail [tz, ty, tx])))

def chkOne (ca cb cc : List (List Bool) → Bool) (tx : List Bool) : Bool :=
  forOps (tavail [tx]) (chkTwo ca cb cc tx)

def chk (ca cb cc : List (List Bool) → Bool) : Bool :=
  forOps (tavail []) (chkOne ca cb cc)

theorem chk_sound (ca cb cc : List (List Bool) → Bool) (h : chk ca cb cc = true)
    (tx ty tz : List Bool) (hx : IsOp (tavail []) tx) (hy : IsOp (tavail [tx]) ty)
    (hz : IsOp (tavail [ty, tx]) tz) (ha : ca (tavail [ty, tx]) = true)
    (hb : cb (tavail [ty, tx]) = true) (hc : cc (tavail [tz, ty, tx]) = true) : False := by
  have hone : chkOne ca cb cc tx = true := forOps_spec (tavail []) (chkOne ca cb cc) h tx hx
  have htwo : chkTwo ca cb cc tx ty = true :=
    forOps_spec (tavail [tx]) (chkTwo ca cb cc tx) hone ty hy
  unfold chkTwo at htwo
  rw [ha, hb] at htwo
  have hthree : forOps (tavail [ty, tx]) (fun tz => !(cc (tavail [tz, ty, tx]))) = true := by
    simpa using htwo
  have hfour : (!(cc (tavail [tz, ty, tx]))) = true :=
    forOps_spec (tavail [ty, tx]) (fun tz => !(cc (tavail [tz, ty, tx]))) hthree tz hz
  rw [hc] at hfour
  exact absurd hfour (by decide)

theorem chk_dpq : chk hasD hasP hasQ = true := by decide +kernel

theorem chk_dqp : chk hasD hasQ hasP = true := by decide +kernel

theorem chk_pqd : chk hasP hasQ hasD = true := by decide +kernel

theorem sep {X : Type} (F H : X → Bool) (x y : X) (hF : F x = F y) (hH : H x ≠ H y)
    (g : X → Bool) (hf : F = g ∨ F = fun z => !(g z)) (hg : H = g ∨ H = fun z => !(g z)) :
    False := by
  rcases hf with hf | hf
  · rcases hg with hg | hg
    · apply hH; rw [hg, ← hf]; exact hF
    · apply hH; rw [hg]
      show (!(g x)) = !(g y)
      rw [← hf, hF]
  · have hgx : g x = g y := by
      have hk := hF
      rw [hf] at hk
      simpa using hk
    rcases hg with hg | hg
    · apply hH; rw [hg]; exact hgx
    · apply hH; rw [hg]
      show (!(g x)) = !(g y)
      rw [hgx]

theorem cov_pt {n : ℕ} (G : Finset (Fin n × Fin n)) (hlt : ∀ e ∈ G, e.1 < e.2) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (habadj : (a, b) ∈ G ∨ (b, a) ∈ G) (hbcadj : (b, c) ∈ G ∨ (c, b) ∈ G)
    (hnac : ¬ ((a, c) ∈ G ∨ (c, a) ∈ G)) (i j k : Bool) :
    CovS G {a, b, c} (pt a b c i j k) ↔ ((i || j) && (j || k)) = true := by
  constructor
  · intro h
    have hij : i = true ∨ j = true := by
      rcases habadj with he | he
      · have hh := h _ he (by simp) (by simp)
        rw [pt_a, pt_b a b c i j k hab] at hh
        exact hh
      · have hh := h _ he (by simp) (by simp)
        rw [pt_a, pt_b a b c i j k hab] at hh
        exact hh.symm
    have hjk : j = true ∨ k = true := by
      rcases hbcadj with he | he
      · have hh := h _ he (by simp) (by simp)
        rw [pt_b a b c i j k hab, pt_c a b c i j k hac hbc] at hh
        exact hh
      · have hh := h _ he (by simp) (by simp)
        rw [pt_b a b c i j k hab, pt_c a b c i j k hac hbc] at hh
        exact hh.symm
    rcases hij with hi | hi <;> rcases hjk with hj | hj <;> simp [hi, hj]
  · intro h e he hea heb
    have hh : (i = true ∨ j = true) ∧ (j = true ∨ k = true) := by
      simpa using h
    have hne : e.1 ≠ e.2 := ne_of_lt (hlt e he)
    have hmem : (e.1, e.2) ∈ G := he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hea heb
    rcases hea with hea | hea | hea <;> rcases heb with heb | heb | heb <;>
      rw [hea, heb] at hmem hne <;> rw [hea, heb]
    all_goals first
      | exact absurd rfl hne
      | exact absurd (Or.inl hmem) hnac
      | exact absurd (Or.inr hmem) hnac
      | (rw [pt_a, pt_b a b c i j k hab]; exact hh.1)
      | (rw [pt_b a b c i j k hab, pt_a]; exact hh.1.symm)
      | (rw [pt_b a b c i j k hab, pt_c a b c i j k hac hbc]; exact hh.2)
      | (rw [pt_c a b c i j k hac hbc, pt_b a b c i j k hab]; exact hh.2.symm)

theorem tbl_av {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (L : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool)
    (hf : Av (BS {a, b, c}) L f) : tblOf a b c f ∈ tavail (L.map (tblOf a b c)) := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hgt : tblOf a b c g ∈ L.map (tblOf a b c) ++ tbase := by
    rcases hg with h | h | h
    · obtain ⟨i, hi, hgi⟩ := (bs_iff _ _).mp h
      apply List.mem_append_right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi | hi
      · rw [hgi, hi]; simp [tblOf, pt, tbase]
      · rw [hgi, hi]; simp [tblOf, pt, tbase, hab.symm]
      · rw [hgi, hi]; simp [tblOf, pt, tbase, hac.symm, hbc.symm]
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨g, h, rfl⟩)
    · apply List.mem_append_right
      rw [h]; simp [tblOf, tbase]
  rcases hfg with hfg | hfg
  · rw [hfg]; exact List.mem_append_left _ hgt
  · rw [hfg]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, hgt, rfl⟩

theorem isop_tr {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (L : List ((Fin n → Bool) → Bool)) (u v g : (Fin n → Bool) → Bool)
    (hu : Av (BS {a, b, c}) L u) (hv : Av (BS {a, b, c}) L v)
    (hg : g = (fun x => u x && v x) ∨ g = (fun x => u x || v x)) :
    IsOp (tavail (L.map (tblOf a b c))) (tblOf a b c g) := by
  refine (isop_iff _ _).mpr ⟨tblOf a b c u, tbl_av a b c hab hbc hac L u hu,
    tblOf a b c v, tbl_av a b c hab hbc hac L v hv, ?_⟩
  rcases hg with hg | hg
  · left; rw [hg]; rfl
  · right; rw [hg]; rfl

theorem pad {X : Type} (B : Set (X → Bool)) :
    ∀ (k : ℕ) (L : List (X → Bool)), Valid B L → L.length + k = 3 →
      ∃ Lt : List (X → Bool), Lt.length = 3 ∧ Valid B Lt ∧ ∀ f, Av B L f → Av B Lt f := by
  intro k
  induction k with
  | zero =>
    intro L hV hl
    exact ⟨L, by omega, hV, fun f hf => hf⟩
  | succ k ih =>
    intro L hV hl
    obtain ⟨Lt, hLt, hVt, hsub⟩ := ih ((fun _ => true) :: L)
      ((valid_cons _ _ _).mpr ⟨hV, _, av_true, _, av_true, Or.inl rfl⟩)
      (by simp only [List.length_cons]; omega)
    exact ⟨Lt, hLt, hVt, fun f hf => hsub f (av_mono _ hf)⟩

theorem base {n : ℕ} (G : Finset (Fin n × Fin n)) (hlt : ∀ e ∈ G, e.1 < e.2) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (habadj : (a, b) ∈ G ∨ (b, a) ∈ G) (hbcadj : (b, c) ∈ G ∨ (c, b) ∈ G)
    (hnac : ¬ ((a, c) ∈ G ∨ (c, a) ∈ G)) :
    ∀ L, Inv G a b c {a, b, c} L → 3 + 1 ≤ L.length := by
  intro L hI
  by_contra hcon
  obtain ⟨hV, ⟨D, hDav, hD⟩, ⟨P, hPav, hP⟩, ⟨Q, hQav, hQ⟩⟩ := hI
  obtain ⟨Lt, hLt, hVt, hsub⟩ := pad (BS {a, b, c}) (3 - L.length) L hV (by omega)
  obtain ⟨gz, gy, gx, hLe⟩ := List.length_eq_three.mp hLt
  rw [hLe] at hVt hsub
  obtain ⟨hVy, uz, huz, vz, hvz, hgz⟩ := (valid_cons _ _ _).mp hVt
  obtain ⟨hVx, uy, huy, vy, hvy, hgy⟩ := (valid_cons _ _ _).mp hVy
  obtain ⟨-, ux, hux, vx, hvx, hgx⟩ := (valid_cons _ _ _).mp hVx
  have eD : ∀ i j k, D (pt a b c i j k) = ((i || j) && (j || k)) := fun i j k =>
    Bool.eq_iff_iff.mpr ((hD _).trans (cov_pt G hlt a b c hab hbc hac habadj hbcadj hnac i j k))
  have eP : ∀ i j k, ((i || j) && (j || k)) = true → P (pt a b c i j k) = xor i j := by
    intro i j k h
    have hh := hP _ ((cov_pt G hlt a b c hab hbc hac habadj hbcadj hnac i j k).mpr h)
    rw [pt_a, pt_b a b c i j k hab] at hh
    exact hh
  have eQ : ∀ i j k, ((i || j) && (j || k)) = true → Q (pt a b c i j k) = xor j k := by
    intro i j k h
    have hh := hQ _ ((cov_pt G hlt a b c hab hbc hac habadj hbcadj hnac i j k).mpr h)
    rw [pt_b a b c i j k hab, pt_c a b c i j k hac hbc] at hh
    exact hh
  have tDeq : tblOf a b c D = tD := by
    simp only [tblOf, eD]
    rfl
  have tPis : isP (tblOf a b c P) = true := by
    simp [isP, tblOf, eP false true false rfl, eP true true false rfl, eP true false true rfl,
      eP false true true rfl, eP true true true rfl]
  have tQis : isQ (tblOf a b c Q) = true := by
    simp [isQ, tblOf, eQ false true false rfl, eQ true true false rfl, eQ true false true rfl,
      eQ false true true rfl, eQ true true true rfl]
  have opx : IsOp (tavail []) (tblOf a b c gx) := isop_tr a b c hab hbc hac [] ux vx gx hux hvx hgx
  have opy : IsOp (tavail [tblOf a b c gx]) (tblOf a b c gy) :=
    isop_tr a b c hab hbc hac [gx] uy vy gy huy hvy hgy
  have opz : IsOp (tavail [tblOf a b c gy, tblOf a b c gx]) (tblOf a b c gz) :=
    isop_tr a b c hab hbc hac [gy, gx] uz vz gz huz hvz hgz
  have hDz := hsub D hDav
  have hPz := hsub P hPav
  have hQz := hsub Q hQav
  have trD : ∀ Lx : List ((Fin n → Bool) → Bool), Av (BS {a, b, c}) Lx D →
      hasD (tavail (Lx.map (tblOf a b c))) = true := by
    intro Lx h
    have hm := tbl_av a b c hab hbc hac Lx D h
    rw [tDeq] at hm
    exact List.any_eq_true.mpr ⟨tD, hm, by simp⟩
  have trP : ∀ Lx : List ((Fin n → Bool) → Bool), Av (BS {a, b, c}) Lx P →
      hasP (tavail (Lx.map (tblOf a b c))) = true := fun Lx h =>
    List.any_eq_true.mpr ⟨_, tbl_av a b c hab hbc hac Lx P h, tPis⟩
  have trQ : ∀ Lx : List ((Fin n → Bool) → Bool), Av (BS {a, b, c}) Lx Q →
      hasQ (tavail (Lx.map (tblOf a b c))) = true := fun Lx h =>
    List.any_eq_true.mpr ⟨_, tbl_av a b c hab hbc hac Lx Q h, tQis⟩
  have sDP : ∀ g : (Fin n → Bool) → Bool, (D = g ∨ D = fun z => !(g z)) →
      (P = g ∨ P = fun z => !(g z)) → False := fun g =>
    sep D P (pt a b c false true false) (pt a b c true true false)
      (by rw [eD, eD]; rfl)
      (by rw [eP false true false rfl, eP true true false rfl]; decide) g
  have sDQ : ∀ g : (Fin n → Bool) → Bool, (D = g ∨ D = fun z => !(g z)) →
      (Q = g ∨ Q = fun z => !(g z)) → False := fun g =>
    sep D Q (pt a b c false true false) (pt a b c true true true)
      (by rw [eD, eD]; rfl)
      (by rw [eQ false true false rfl, eQ true true true rfl]; decide) g
  have sPQ : ∀ g : (Fin n → Bool) → Bool, (P = g ∨ P = fun z => !(g z)) →
      (Q = g ∨ Q = fun z => !(g z)) → False := fun g =>
    sep P Q (pt a b c true true false) (pt a b c true true true)
      (by rw [eP true true false rfl, eP true true true rfl])
      (by rw [eQ true true false rfl, eQ true true true rfl]; decide) g
  rcases av_cons_cases hDz with hd | hd
  · rcases av_cons_cases hPz with hp | hp
    · exact chk_sound hasD hasP hasQ chk_dpq _ _ _ opx opy opz (trD [gy, gx] hd)
        (trP [gy, gx] hp) (trQ [gz, gy, gx] hQz)
    · rcases av_cons_cases hQz with hq | hq
      · exact chk_sound hasD hasQ hasP chk_dqp _ _ _ opx opy opz (trD [gy, gx] hd)
          (trQ [gy, gx] hq) (trP [gz, gy, gx] hPz)
      · exact sPQ gz hp hq
  · rcases av_cons_cases hPz with hp | hp
    · rcases av_cons_cases hQz with hq | hq
      · exact chk_sound hasP hasQ hasD chk_pqd _ _ _ opx opy opz (trP [gy, gx] hp)
          (trQ [gy, gx] hq) (trD [gz, gy, gx] hDz)
      · exact sDQ gz hd hq
    · exact sDP gz hd hp

-- Part D: circuits as derivations

def inp {n : ℕ} (x : Fin n → Bool) : List Bool := List.ofFn x ++ [false, true]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem inp_len {n : ℕ} (x : Fin n → Bool) : (inp x).length = n + 2 := by
  simp [inp]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : i < l.length
  · rw [List.getElem?_append_left h, if_pos h]
  · rw [if_neg h, List.getElem?_append_right (Nat.le_of_not_lt h)]
    by_cases e : i = l.length
    · rw [if_pos e, e]; simp
    · rw [if_neg e]
      have hk : i - l.length = (i - l.length - 1) + 1 := by omega
      rw [hk]; simp

theorem inp_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (inp x).getD i false = if h : i < n then x ⟨i, h⟩ else decide (i = n + 1) := by
  unfold inp
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · have hw : i < (List.ofFn x).length := by simpa using h
    rw [List.getElem?_append_left hw, List.getElem?_eq_getElem hw, List.getElem_ofFn, dif_pos h]
    rfl
  · have hw : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt h
    rw [List.getElem?_append_right hw, dif_neg h]
    have hl : (List.ofFn x).length = n := by simp
    rw [hl]
    obtain ⟨k, hk⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    rw [hk, Nat.add_sub_cancel_left]
    rcases k with _ | _ | k <;> simp

def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  unfold isNot
  cases g.op <;> simp

theorem nc_eq (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter isNot).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases hg : g.op <;> simp [isNot, hg]

theorem nc_snoc_other (gs : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    ((gs ++ [g]).filter isNot).length =
      (gs.filter isNot).length := by
  have hk : isNot g = false := by
    rw [Bool.eq_false_iff]
    exact fun hh => h ((isNot_iff g).mp hh)
  rw [List.filter_append]; simp [hk]

theorem nc_snoc_not (gs : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    ((gs ++ [g]).filter isNot).length =
      (gs.filter isNot).length + 1 := by
  have hk : isNot g = true := (isNot_iff g).mpr h
  rw [List.filter_append]; simp [hk]

theorem circuit_deriv {n : ℕ} (gs : List Gate)
    (hf : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∃ L : List ((Fin n → Bool) → Bool), Valid (BS (Finset.univ : Finset (Fin n))) L ∧
      L.length + (gs.filter isNot).length = gs.length ∧
      ∀ i : ℕ, Av (BS (Finset.univ : Finset (Fin n))) L
        (fun x => (gs.foldl stepW (inp x)).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], valid_nil _, by simp, fun i => ?_⟩
    show Av (BS (Finset.univ : Finset (Fin n))) [] (fun x : Fin n → Bool => (inp x).getD i false)
    by_cases hi : i < n
    · have he : (fun x : Fin n → Bool => (inp x).getD i false) = fun x => x ⟨i, hi⟩ := by
        funext x
        rw [inp_getD, dif_pos hi]
      rw [he]
      exact av_gen (Or.inl ((bs_iff _ _).mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩))
    · by_cases hj : i = n + 1
      · have he : (fun x : Fin n → Bool => (inp x).getD i false) = fun _ => true := by
          funext x
          rw [inp_getD, dif_neg hi]
          simp [hj]
        rw [he]; exact av_true
      · have he : (fun x : Fin n → Bool => (inp x).getD i false) = fun _ => false := by
          funext x
          rw [inp_getD, dif_neg hi]
          simp [hj]
        rw [he]; exact av_false
  | append_singleton gs g ih =>
    obtain ⟨L, hV, hlen, hav⟩ := ih (fun gp hgp => hf gp (List.mem_append_left _ hgp))
    obtain ⟨hop, hfan⟩ := hf g (by simp)
    have hlenW : ∀ x : Fin n → Bool, (gs.foldl stepW (inp x)).length = n + 2 + gs.length := by
      intro x; rw [fold_len, inp_len]
    have key : ∀ (Lp : List ((Fin n → Bool) → Bool)) (val : (Fin n → Bool) → Bool),
        (∀ f, Av (BS (Finset.univ : Finset (Fin n))) L f →
          Av (BS (Finset.univ : Finset (Fin n))) Lp f) →
        Av (BS (Finset.univ : Finset (Fin n))) Lp val →
        (∀ x, val x = g.op.eval (g.inputs.map fun j => (gs.foldl stepW (inp x)).getD j false)) →
        ∀ i : ℕ, Av (BS (Finset.univ : Finset (Fin n))) Lp
          (fun x => ((gs ++ [g]).foldl stepW (inp x)).getD i false) := by
      intro Lp val hsub hval hveq i
      have hstep : ∀ x : Fin n → Bool, ((gs ++ [g]).foldl stepW (inp x)).getD i false =
          if i < n + 2 + gs.length then (gs.foldl stepW (inp x)).getD i false
          else if i = n + 2 + gs.length then val x else false := by
        intro x
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        show ((gs.foldl stepW (inp x)) ++
          [g.op.eval (g.inputs.map fun j => (gs.foldl stepW (inp x)).getD j false)]).getD i false = _
        rw [getD_snoc, hlenW x, hveq x]
      by_cases hi : i < n + 2 + gs.length
      · have he : (fun x : Fin n → Bool => ((gs ++ [g]).foldl stepW (inp x)).getD i false) =
            fun x => (gs.foldl stepW (inp x)).getD i false := by
          funext x; rw [hstep x, if_pos hi]
        rw [he]; exact hsub _ (hav i)
      · by_cases hj : i = n + 2 + gs.length
        · have he : (fun x : Fin n → Bool => ((gs ++ [g]).foldl stepW (inp x)).getD i false) =
              val := by
            funext x; rw [hstep x, if_neg hi, if_pos hj]
          rw [he]; exact hval
        · have he : (fun x : Fin n → Bool => ((gs ++ [g]).foldl stepW (inp x)).getD i false) =
              fun _ => false := by
            funext x; rw [hstep x, if_neg hi, if_neg hj]
          rw [he]; exact av_false
    by_cases hnot : g.op = GateOp.not
    · obtain ⟨val, hval, hveq⟩ : ∃ val : (Fin n → Bool) → Bool,
          Av (BS (Finset.univ : Finset (Fin n))) L val ∧
          ∀ x, val x = g.op.eval (g.inputs.map fun j => (gs.foldl stepW (inp x)).getD j false) := by
        rcases hin : g.inputs with _ | ⟨i, r⟩
        · exact ⟨fun _ => true, av_true, fun x => by rw [hnot]; rfl⟩
        · exact ⟨fun x => !((gs.foldl stepW (inp x)).getD i false), av_not (hav i),
            fun x => by rw [hnot]; rfl⟩
      refine ⟨L, hV, ?_, key L val (fun f hf => hf) hval hveq⟩
      rw [nc_snoc_not gs g hnot, List.length_append, List.length_singleton]
      omega
    · obtain ⟨val, u, v, hu, hv, hval, hveq⟩ : ∃ val u v : (Fin n → Bool) → Bool,
          Av (BS (Finset.univ : Finset (Fin n))) L u ∧
          Av (BS (Finset.univ : Finset (Fin n))) L v ∧
          (val = (fun x => u x && v x) ∨ val = (fun x => u x || v x)) ∧
          ∀ x, val x = g.op.eval (g.inputs.map fun j => (gs.foldl stepW (inp x)).getD j false) := by
        rcases hop with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
          · exact ⟨fun _ => true, fun _ => true, fun _ => true, av_true, av_true, Or.inl rfl,
              fun x => by rw [hop]; rfl⟩
          · exact ⟨fun x => (gs.foldl stepW (inp x)).getD i false && true, _, fun _ => true,
              hav i, av_true, Or.inl rfl, fun x => by rw [hop]; rfl⟩
          · exact ⟨fun x => (gs.foldl stepW (inp x)).getD i false &&
                (gs.foldl stepW (inp x)).getD j false, _, _,
              hav i, hav j, Or.inl rfl, fun x => by rw [hop]; simp [GateOp.eval]⟩
          · exfalso
            rw [hin] at hfan
            simp only [List.length_cons] at hfan
            omega
        · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
          · exact ⟨fun _ => false, fun _ => false, fun _ => false, av_false, av_false, Or.inr rfl,
              fun x => by rw [hop]; rfl⟩
          · exact ⟨fun x => (gs.foldl stepW (inp x)).getD i false || false, _, fun _ => false,
              hav i, av_false, Or.inr rfl, fun x => by rw [hop]; rfl⟩
          · exact ⟨fun x => (gs.foldl stepW (inp x)).getD i false ||
                (gs.foldl stepW (inp x)).getD j false, _, _,
              hav i, hav j, Or.inr rfl, fun x => by rw [hop]; simp [GateOp.eval]⟩
          · exfalso
            rw [hin] at hfan
            simp only [List.length_cons] at hfan
            omega
        · exact absurd hop hnot
      refine ⟨val :: L, (valid_cons _ _ _).mpr ⟨hV, u, hu, v, hv, hval⟩, ?_,
        key _ val (fun f hf => av_mono _ hf)
          (av_gen (Or.inr (Or.inl (List.mem_cons.mpr (Or.inl rfl))))) hveq⟩
      rw [nc_snoc_other gs g hnot, List.length_cons, List.length_append, List.length_singleton]
      omega

-- Part E: two NOT gates

def stepN (s : List Bool × List Bool) (g : Gate) : List Bool × List Bool :=
  (stepW s.1 g,
    if isNot g = true then s.2 ++ [g.op.eval (g.inputs.map fun i => s.1.getD i false)]
    else s.2)

theorem runN_fst (gs : List Gate) (s : List Bool × List Bool) :
    (gs.foldl stepN s).1 = gs.foldl stepW s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    rfl

def LeW (w v : List Bool) : Prop := ∀ i, w.getD i false = true → v.getD i false = true

theorem le_snoc (l m : List Bool) (v w : Bool) (h : LeW l m) (hlen : l.length = m.length)
    (hv : v = true → w = true) : LeW (l ++ [v]) (m ++ [w]) := by
  intro i
  rw [getD_snoc, getD_snoc, hlen]
  by_cases hi : i < m.length
  · rw [if_pos hi, if_pos hi]; exact h i
  · rw [if_neg hi, if_neg hi]
    by_cases hj : i = m.length
    · rw [if_pos hj, if_pos hj]; exact hv
    · rw [if_neg hj, if_neg hj]; exact id

theorem all_mono (ins : List ℕ) (l m : List Bool) (h : LeW l m) :
    GateOp.and.eval (ins.map fun i => l.getD i false) = true →
      GateOp.and.eval (ins.map fun i => m.getD i false) = true := by
  intro ha
  have hb : (ins.map fun i => l.getD i false).all id = true := ha
  show (ins.map fun i => m.getD i false).all id = true
  rw [List.all_eq_true] at hb ⊢
  intro z hz
  obtain ⟨i, hi, hzi⟩ := List.mem_map.mp hz
  rw [← hzi]
  exact h i (hb _ (List.mem_map.mpr ⟨i, hi, rfl⟩))

theorem any_mono (ins : List ℕ) (l m : List Bool) (h : LeW l m) :
    GateOp.or.eval (ins.map fun i => l.getD i false) = true →
      GateOp.or.eval (ins.map fun i => m.getD i false) = true := by
  intro ha
  have hb : (ins.map fun i => l.getD i false).any id = true := ha
  show (ins.map fun i => m.getD i false).any id = true
  rw [List.any_eq_true] at hb ⊢
  obtain ⟨z, hz, hzt⟩ := hb
  obtain ⟨i, hi, hzi⟩ := List.mem_map.mp hz
  rw [← hzi] at hzt
  exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hzt⟩

theorem mono_three (gs : List Gate)
    (hf : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hc : (gs.filter isNot).length ≤ 1)
    (w v : List Bool) (hlen : w.length = v.length) (hle : LeW w v) :
    (LeW (gs.foldl stepN (w, [])).1 (gs.foldl stepN (v, [])).1 ∧
      ((gs.filter isNot).length = 1 ∨
        ((gs.foldl stepN (w, [])).2 = [] ∧ (gs.foldl stepN (v, [])).2 = []))) ∨
    ((gs.filter isNot).length = 1 ∧
      (gs.foldl stepN (w, [])).2 = [true] ∧ (gs.foldl stepN (v, [])).2 = [false]) := by
  induction gs using List.reverseRecOn with
  | nil => exact Or.inl ⟨hle, Or.inr ⟨rfl, rfl⟩⟩
  | append_singleton gs g ih =>
    have hop := hf g (by simp)
    have hfp : ∀ gp ∈ gs, gp.op = GateOp.and ∨ gp.op = GateOp.or ∨ gp.op = GateOp.not :=
      fun gp hgp => hf gp (List.mem_append_left _ hgp)
    have hl : (gs.foldl stepN (w, [])).1.length = (gs.foldl stepN (v, [])).1.length := by
      rw [runN_fst, runN_fst, fold_len, fold_len]
      show w.length + gs.length = v.length + gs.length
      rw [hlen]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil]
    by_cases hnot : g.op = GateOp.not
    · rw [nc_snoc_not gs g hnot] at hc ⊢
      rcases ih hfp (by omega) with ⟨hlea, hx | ⟨hsa, hsb⟩⟩ | ⟨hx, _⟩
      · omega
      · by_cases hv : (g.op.eval (g.inputs.map fun i => (gs.foldl stepN (w, [])).1.getD i false) = true →
            g.op.eval (g.inputs.map fun i => (gs.foldl stepN (v, [])).1.getD i false) = true)
        · left
          exact ⟨le_snoc _ _ _ _ hlea hl hv, Or.inl (by omega)⟩
        · right
          have hvt : g.op.eval (g.inputs.map fun i => (gs.foldl stepN (w, [])).1.getD i false) = true ∧
              g.op.eval (g.inputs.map fun i => (gs.foldl stepN (v, [])).1.getD i false) = false := by
            constructor
            · by_contra hh
              exact hv (fun hk => absurd hk hh)
            · by_contra hh
              exact hv (fun _ => by simpa using hh)
          refine ⟨by omega, ?_, ?_⟩
          · show (if isNot g = true then (gs.foldl stepN (w, [])).2 ++
              [g.op.eval (g.inputs.map fun i => (gs.foldl stepN (w, [])).1.getD i false)]
              else (gs.foldl stepN (w, [])).2) = [true]
            rw [if_pos ((isNot_iff g).mpr hnot), hsa, hvt.1]
            rfl
          · show (if isNot g = true then (gs.foldl stepN (v, [])).2 ++
              [g.op.eval (g.inputs.map fun i => (gs.foldl stepN (v, [])).1.getD i false)]
              else (gs.foldl stepN (v, [])).2) = [false]
            rw [if_pos ((isNot_iff g).mpr hnot), hsb, hvt.2]
            rfl
      · omega
    · rw [nc_snoc_other gs g hnot] at hc ⊢
      have hneg : ¬ (isNot g = true) := fun hh => hnot ((isNot_iff g).mp hh)
      have hsw : (stepN (gs.foldl stepN (w, [])) g).2 = (gs.foldl stepN (w, [])).2 := by
        show (if isNot g = true then _ else _) = _
        exact if_neg hneg
      have hsv : (stepN (gs.foldl stepN (v, [])) g).2 = (gs.foldl stepN (v, [])).2 := by
        show (if isNot g = true then _ else _) = _
        exact if_neg hneg
      rw [hsw, hsv]
      rcases ih hfp hc with ⟨hlea, hx⟩ | hx
      · left
        refine ⟨le_snoc _ _ _ _ hlea hl ?_, hx⟩
        rcases hop with h | h | h
        · rw [h]; exact all_mono _ _ _ hlea
        · rw [h]; exact any_mono _ _ _ hlea
        · exact absurd h hnot
      · right; exact hx

theorem inp_le {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    LeW (inp x) (inp y) := by
  intro i
  rw [inp_getD, inp_getD]
  by_cases hi : i < n
  · rw [dif_pos hi, dif_pos hi]; exact h _
  · rw [dif_neg hi, dif_neg hi]; exact id

theorem not_two {n : ℕ} (G : Finset (Fin n × Fin n)) (hlt : ∀ e ∈ G, e.1 < e.2) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hnac : ¬ ((a, c) ∈ G ∨ (c, a) ∈ G))
    (gs : List Gate) (pw qw : ℕ)
    (hf : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (key : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      (gs.foldl stepW (inp x)).getD pw false = xor (x a) (x b) ∧
      (gs.foldl stepW (inp x)).getD qw false = xor (x b) (x c)) :
    2 ≤ (gs.filter isNot).length := by
  by_contra hcon
  have hc : (gs.filter isNot).length ≤ 1 := by omega
  obtain ⟨xa, hxa⟩ : ∃ xa : Fin n → Bool, xa = fun v => !(decide (v = a) || decide (v = c)) :=
    ⟨_, rfl⟩
  obtain ⟨xb, hxb⟩ : ∃ xb : Fin n → Bool, xb = fun v => !(decide (v = c)) := ⟨_, rfl⟩
  have hcova : ∀ e ∈ G, xa e.1 = true ∨ xa e.2 = true := by
    intro e he
    have hne : e.1 ≠ e.2 := ne_of_lt (hlt e he)
    have hm : (e.1, e.2) ∈ G := he
    by_cases hp : e.1 = a ∨ e.1 = c
    · right
      have hna : e.2 ≠ a := by
        intro hh
        rcases hp with hp | hp
        · exact hne (hp.trans hh.symm)
        · rw [hp, hh] at hm; exact hnac (Or.inr hm)
      have hnc : e.2 ≠ c := by
        intro hh
        rcases hp with hp | hp
        · rw [hp, hh] at hm; exact hnac (Or.inl hm)
        · exact hne (hp.trans hh.symm)
      rw [hxa]; simp [hna, hnc]
    · left
      have hpa : e.1 ≠ a := fun hh => hp (Or.inl hh)
      have hpc : e.1 ≠ c := fun hh => hp (Or.inr hh)
      rw [hxa]; simp [hpa, hpc]
  have hcovb : ∀ e ∈ G, xb e.1 = true ∨ xb e.2 = true := by
    intro e he
    have hne : e.1 ≠ e.2 := ne_of_lt (hlt e he)
    by_cases hp : e.1 = c
    · right
      have hnc : e.2 ≠ c := fun hh => hne (hp.trans hh.symm)
      rw [hxb]; simp [hnc]
    · left; rw [hxb]; simp [hp]
  have hcovc : ∀ e ∈ G, (fun _ : Fin n => true) e.1 = true ∨ (fun _ : Fin n => true) e.2 = true :=
    fun e _ => Or.inl rfl
  obtain ⟨hpa, -⟩ := key xa hcova
  obtain ⟨hpb, hqb⟩ := key xb hcovb
  obtain ⟨-, hqc⟩ := key (fun _ : Fin n => true) hcovc
  have hpat : (gs.foldl stepW (inp xa)).getD pw false = true := by
    rw [hpa, hxa]; simp [hab.symm, hbc]
  have hpbf : (gs.foldl stepW (inp xb)).getD pw false = false := by
    rw [hpb, hxb]; simp [hac, hbc]
  have hqbt : (gs.foldl stepW (inp xb)).getD qw false = true := by
    rw [hqb, hxb]; simp [hbc]
  have hqcf : (gs.foldl stepW (inp (fun _ : Fin n => true))).getD qw false = false := by
    rw [hqc]; simp
  have lab : LeW (inp xa) (inp xb) := by
    apply inp_le
    intro i hi
    rw [hxa] at hi
    rw [hxb]
    simp at hi ⊢
    exact hi.2
  have lbc : LeW (inp xb) (inp (fun _ : Fin n => true)) := inp_le _ _ (fun _ _ => rfl)
  have ea : ∀ x : Fin n → Bool, (gs.foldl stepN (inp x, [])).1 = gs.foldl stepW (inp x) :=
    fun x => runN_fst gs _
  rcases mono_three gs hf hc (inp xa) (inp xb) (by rw [inp_len, inp_len]) lab with
    ⟨hle, _⟩ | ⟨_, _, hnb⟩
  · rw [ea, ea] at hle
    have hh := hle pw hpat
    rw [hpbf] at hh
    exact absurd hh (by decide)
  · rcases mono_three gs hf hc (inp xb) (inp (fun _ : Fin n => true))
        (by rw [inp_len, inp_len]) lbc with ⟨hle, _⟩ | ⟨_, hna, _⟩
    · rw [ea, ea] at hle
      have hh := hle qw hqbt
      rw [hqcf] at hh
      exact absurd hh (by decide)
    · rw [hna] at hnb
      exact absurd hnb (by decide)

end PEqualNP.Outside.L_lib_1208

open PEqualNP.Outside.L_lib_1208
theorem PEqualNP.Outside.L_lib_1208 : ∀ (n : Nat) (G : Finset (Fin n × Fin n)) (a b c : Fin n),
  (∀ e ∈ G, e.1 < e.2) →
  let adj := fun i j : Fin n => (i,j) ∈ G ∨ (j,i) ∈ G
  (∀ i j : Fin n, Relation.ReflTransGen adj i j) →
  a ≠ b → b ≠ c → a ≠ c → adj a b → adj b c → ¬ adj a c →
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
    C.output < n+2+C.size →
    (∀ x : Fin n → Bool,
      let w := List.ofFn x ++ [false,true]
      let cover := decide (∀ e ∈ G, x e.1 = true ∨ x e.2 = true)
      C.eval w = cover ∧ (cover = true →
        (C.wires w).getD p.val false = xor (x a) (x b) ∧
        (C.wires w).getD q.val false = xor (x b) (x c))) →
    n+3 ≤ C.size ∧ n+1 ≤ C.size - PEqualNP.NotBracket.notCount C ∧
      2 ≤ PEqualNP.NotBracket.notCount C := by
  intro n G a b c hlt adj hconn hab hbc hac habadj hbcadj hnac C p q hfan hrb hout hC
  have hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have hh := hfan g hg
    refine ⟨?_, hh.2⟩
    have hop := hh.1
    simpa [Set.mem_insert_iff] using hop
  have key : ∀ x : Fin n → Bool,
      (C.gates.foldl stepW (inp x)).getD C.output false =
        decide (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
      ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        (C.gates.foldl stepW (inp x)).getD p.val false = xor (x a) (x b) ∧
        (C.gates.foldl stepW (inp x)).getD q.val false = xor (x b) (x c)) :=
    fun x => ⟨(hC x).1, fun hcov => (hC x).2 (decide_eq_true hcov)⟩
  obtain ⟨L, hV, hlenL, hav⟩ := circuit_deriv (n := n) C.gates hgates
  have hInv : Inv G a b c Finset.univ L := by
    refine (inv_iff _ _ _ _ _ _).mpr ⟨hV, ⟨_, hav C.output, fun x => ?_⟩,
      ⟨_, hav p.val, fun x hx => ?_⟩, ⟨_, hav q.val, fun x hx => ?_⟩⟩
    · show (C.gates.foldl stepW (inp x)).getD C.output false = true ↔ _
      rw [(key x).1, decide_eq_true_iff]
      exact ⟨fun h e he _ _ => h e he,
        fun h e he => h e he (Finset.mem_univ _) (Finset.mem_univ _)⟩
    · exact ((key x).2 (fun e he => hx e he (Finset.mem_univ _) (Finset.mem_univ _))).1
    · exact ((key x).2 (fun e he => hx e he (Finset.mem_univ _) (Finset.mem_univ _))).2
  have hcard : ({a, b, c} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hbase : ∀ Lx, Inv G a b c {a, b, c} Lx →
      ({a, b, c} : Finset (Fin n)).card + 1 ≤ Lx.length := by
    intro Lx hLx
    rw [hcard]
    exact base G hlt a b c hab hbc hac habadj hbcadj hnac Lx hLx
  have hmain : n + 1 ≤ L.length :=
    grow G hlt a b c hconn habadj (n - 3) {a, b, c} (by simp) (by simp) (by simp)
      (by rw [hcard]) hbase L hInv
  have hnot : 2 ≤ (C.gates.filter isNot).length :=
    not_two G hlt a b c hab hbc hac hnac C.gates p.val q.val (fun g hg => (hgates g hg).1)
      (fun x hcov => (key x).2 hcov)
  have hnc : PEqualNP.NotBracket.notCount C =
      (C.gates.filter isNot).length := nc_eq C
  have hsz : C.size = C.gates.length := rfl
  rw [hnc, hsz]
  omega
