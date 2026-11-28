import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43472

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808426 * 2 ^ 32 + 4272482944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x00004015009b0ab0#64 ++ 0x400004015009b0ab#64 ++ 0xe023ce3f01ff1fff#64 ++ 0xbe023ce3f01ff1ff#64 : BitVec 256),
   (0x10cd14cc86456656#64 ++ 0x810cd14cc8645665#64 ++ 0xf1dd35cc8e47e67f#64 ++ 0x6f1dd35cc8e47e67#64 : BitVec 256),
   (0x26162970b068b863#64 ++ 0x026162970b068b86#64 ++ 0xbe1e39f0f078f87e#64 ++ 0xfbe1e39f0f078f87#64 : BitVec 256),
   (0x0b603e005b00d504#64 ++ 0x00b603e005b00d50#64 ++ 0x6fe03e00ff80ff8d#64 ++ 0xf6fe03e00ff80ff8#64 : BitVec 256),
   (0x4dbfc000edf60008#64 ++ 0x04dbfc000edf6000#64 ++ 0x4fffc000ffff000b#64 ++ 0xf4fffc000ffff000#64 : BitVec 256),
   (0x8ffbbfaa00000000#64 ++ 0x08ffbbfaa0000000#64 ++ 0x9fffffff00000007#64 ++ 0xe9fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [10, 6]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000400000920000 0x0000040000092000 0x4023c00001ff000b 0xb4023c00001ff000

def z1 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe023ce3f01ff1fff 0xbe023ce3f01ff1ff

def z2 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe03e00ff80ff8d 0xf6fe03e00ff80ff8

def z3 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd35cc8e47e67f 0x6f1dd35cc8e47e67

def z4 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e39f0f078f87e 0xfbe1e39f0f078f87

def z5 : W := mkw 0x4dbf8000ed640008 0x04dbf8000ed64000 0x0fdc0000fe000000 0x40fdc0000fe00000

def z6 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fffffff00000007 0xe9fffffff0000000

def z7 : W := mkw 0x008d000084440000 0x0008d00008444000 0x41dd00008e47000b 0x641dd00008e47000

def z8 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffc000ffff000b 0xf4fffc000ffff000

def z9 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xffffffffff80ff8f 0xfffffffffff80ff8

def z10 : W := mkw 0x82403faa00000000 0x082403faa0000000 0x90003fff00000004 0x090003fff0000000

def z11 : W := mkw 0x0b603e0049000000 0x00b603e004900000 0x4fe03e00ff80000d 0xf4fe03e00ff80000

def z12 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0xa0000e3f00001ff4 0x0a0000e3f00001ff

def z13 : W := mkw 0x40044000edf60008 0x040044000edf6000 0x40000000ffff0008 0x140000000ffff000

def z14 : W := mkw 0x0920000049000000 0x0092000004900000 0x4fe00000ff800009 0xf4fe00000ff80000

def z15 : W := mkw 0x00c9148802004404 0x000c914880200440 0xf1dd35cc8e00e60f 0x6f1dd35cc8e00e60

def z16 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901fc1ff00000002 0x0901fc1ff0000000

def z17 : W := mkw 0x94df95ee86456656 0x894df95ee8645665 0xf1dff5ff8e47e67f 0x6f1dff5ff8e47e67

def z18 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0x0022ca3301b81980 0x90022ca3301b8198

def z19 : W := mkw 0x10cd14c886446446 0x810cd14c88644644 0x11dc31c08e00e000 0x411dc31c08e00e00

def z20 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fdc0000ffff0008 0x54fdc0000ffff000

def z21 : W := mkw 0xcdbfc1aaedf60008 0x0cdbfc1aaedf6000 0xdfffc1ffffff000b 0xfdfffc1ffffff000

def z22 : W := mkw 0x0004405580db2af2 0x40004405580db2af 0xf03fffff81ffffff 0xff03fffff81fffff

def z23 : W := mkw 0x849bc1bf009b0ab0 0x4849bc1bf009b0ab 0x901fc1ff007f0072 0x0901fc1ff007f007

def z24 : W := mkw 0x20040050a0682863 0x020040050a068286 0x0000000000780070 0x0000000000078007

def z25 : W := mkw 0x6fbfe970fdfeb86b 0x06fbfe970fdfeb86 0xfffff9f0fffff87f 0xffffff9f0fffff87

def z26 : W := mkw 0x092000005b00d504 0x0092000005b00d50 0x6fe00000ff80ff89 0xf6fe00000ff80ff8

def z27 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xc023c63f01ff07f3 0x0c023c63f01ff07f

def z28 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x71dc31c08e47e678 0x471dc31c08e47e67

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x8023ce3f00000007 0xa8023ce3f0000000

def z30 : W := mkw 0x8ffbffbf009b0ab0 0x48ffbffbf009b0ab 0xffffffff01ff1fff 0xfffffffff01ff1ff

def z31 : W := mkw 0x04160000a0600000 0x004160000a060000 0x0e1e0000f078000a 0xf0e1e0000f078000

def z32 : W := mkw 0x104014cc02016656 0x8104014cc0201665 0xb00035cc0000e674 0x0b00035cc0000e67

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x0022ca3300000000 0x80022ca330000000

def z34 : W := mkw 0x0b202a005b00d504 0x00b202a005b00d50 0x6e200a00ff80ff88 0x96e200a00ff80ff8

def z35 : W := mkw 0x0200281010089820 0x0020028101008982 0xae023830f078f87e 0xfae023830f078f87

def z36 : W := mkw 0x10cd14c886446446 0x810cd14c88644644 0x71dc35c08e00e60d 0x671dc35c08e00e60

def z37 : W := mkw 0x26166975b0fbbaf3 0x426166975b0fbbaf 0xfe1e39f0f1fffffe 0xffe1e39f0f1fffff

def z38 : W := mkw 0x8ffbbfaa4b004504 0x08ffbbfaa4b00450 0xdfffffff0f800787 0xedfffffff0f80078

def z39 : W := mkw 0x5dffd4cceff7665e 0x85dffd4cceff7665 0xfffff5ccffffe67f 0xffffff5ccffffe67

def z40 : W := mkw 0xdfffffeeeff7665e 0x8dfffffeeeff7665 0xffffffffffffe67f 0xfffffffffffffe67

def z41 : W := mkw 0x0dbf800084440000 0x00dbf80008444000 0x4fffc0008e47000b 0xe4fffc0008e47000

def z42 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fde39f000000006 0xe9fde39f00000000

def z43 : W := mkw 0x0000400500930290 0x4000040050093029 0x4021c60f01870781 0x04021c60f0187078

def z44 : W := mkw 0x26162960b060b043 0x026162960b060b04 0x1e1c31c0f000e000 0x41e1c31c0f000e00

def z45 : W := mkw 0x0412012000000000 0x0041201200000000 0x901e01f000000002 0x0901e01f00000000

def z46 : W := mkw 0x00c9148800000000 0x000c914880000000 0x91dd35cc00000007 0x691dd35cc0000000

def z47 : W := mkw 0x0004004080402042 0x0000400408040204 0x200000008040e078 0x0200000008040e07

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x60200e0001801f8d 0xb60200e0001801f8

def z49 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x9e1e31f0f078e072 0x49e1e31f0f078e07

def z50 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x6fffce00ffff1f8f 0xf6fffce00ffff1f8

def z51 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x1ffff1c000000003 0xe1ffff1c00000000

def z52 : W := mkw 0x4dbf8000ed640008 0x04dbf8000ed64000 0x0fffc000fe000003 0xe0fffc000fe00000

def z53 : W := mkw 0x0b202a0000000000 0x00b202a000000000 0x0e200a0000000000 0x80e200a000000000

def z54 : W := mkw 0x8b603faa00000000 0x08b603faa0000000 0x9fe03fff00000005 0xe9fe03fff0000000

def z55 : W := mkw 0x0dfb948800000000 0x00dfb94880000000 0x9ffff5cc00000007 0xe9ffff5cc0000000

def z56 : W := mkw 0x06162920a0600000 0x006162920a060000 0x9e1e39f0f078000e 0xf9e1e39f0f078000

def z57 : W := mkw 0x4ffffe00fff6d50c 0x04ffffe00fff6d50 0x4ffff000ffffe00b 0xf4ffff000ffffe00

def z58 : W := mkw 0x02403e001200d504 0x002403e001200d50 0x20003e000000ff84 0x020003e000000ff8

def z59 : W := mkw 0x2f362970f968b863 0x02f362970f968b86 0xfffe39f0fff8f87f 0xffffe39f0fff8f87

def z60 : W := mkw 0x49adc000cdd60008 0x049adc000cdd6000 0x41fdc0008fc7000b 0x641fdc0008fc7000

def z61 : W := mkw 0x0612292000000000 0x0061229200000000 0x0e02083000000000 0x80e0208300000000

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000000040007e 0x2a00000000040007

def z63 : W := mkw 0x00000011000808a0 0x400000011000808a 0x00000a3300001980 0x000000a330000198

def z64 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x9e1e09f070781872 0x99e1e09f07078187

def z65 : W := mkw 0x220029701008b863 0x0220029701008b86 0xb00039f00000f874 0x0b00039f00000f87

def z66 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x0fc03000fe00e000 0x40fc03000fe00e00

def z67 : W := mkw 0x0612292010009000 0x0061229201000900 0xbe1e39f0f000f80e 0xfbe1e39f0f000f80

def z68 : W := mkw 0x8f32ab2259009100 0x08f32ab225900910 0x0e22ca3371801980 0x90e22ca337180198

def z69 : W := mkw 0x0000400500930290 0x4000040050093029 0xc023ce3f01870787 0xac023ce3f0187078

def z70 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903fcfff00000007 0xa903fcfff0000000

def z71 : W := mkw 0x4d32c00069b20008 0x04d32c00069b2000 0x4e23c00071ff000b 0xb4e23c00071ff000

def z72 : W := mkw 0x0200280010009000 0x0020028001000900 0x2e003800f000f80c 0xf2e003800f000f80

def z73 : W := mkw 0x8dfb97aa00000000 0x08dfb97aa0000000 0x91ffc7ff00000003 0x091ffc7ff0000000

def z74 : W := mkw 0xafffbffafb68fd67 0x0afffbffafb68fd6 0xfffffffffff8ffff 0xffffffffffff8fff

def z75 : W := mkw 0x1004004486456656 0x8100400448645665 0x600000008e47e678 0x0600000008e47e67

def z76 : W := mkw 0x0004004080402042 0x0000400408040204 0xb01c31c08040e07e 0x6b01c31c08040e07

def z77 : W := mkw 0x10c9148c06054614 0x810c9148c0605461 0x41c1040c0e070601 0x041c1040c0e07060

def z78 : W := mkw 0x8ffbbfaa02004404 0x08ffbbfaa0200440 0xffffffff8e00e60f 0xeffffffff8e00e60

def z79 : W := mkw 0x2412013020280821 0x0241201302028082 0x0002003000380000 0x0000200300038000

def z80 : W := mkw 0x36df3dfcb66dfe77 0x836df3dfcb66dfe7 0xffdf3dfcfe7ffe7f 0xfffdf3dfcfe7ffe7

def z81 : W := mkw 0x2200293010089821 0x0220029301008982 0x0000083000001800 0x0000008300000180

def z82 : W := mkw 0x9fffbfea86446446 0x89fffbfea8644644 0x1fdc31c08e00e000 0x41fdc31c08e00e00

def z83 : W := mkw 0x0000001000080820 0x0000000100008082 0xa00208300078187e 0xba00208300078187

def z84 : W := mkw 0x40044015edff0ab8 0x440044015edff0ab 0x60000000ffff1ff8 0x160000000ffff1ff

def z85 : W := mkw 0x3fff3ffcff6dff77 0x83fff3ffcff6dff7 0xffff3ffcffffffff 0xfffff3ffcfffffff

def z86 : W := mkw 0x4dbfc010edfe0828 0x04dbfc010edfe082 0xefffc830ffff187f 0xfefffc830ffff187

def z87 : W := mkw 0x2612693130ba98a1 0x42612693130ba98a 0x0e22ca3371b81980 0x90e22ca3371b8198

def z88 : W := mkw 0x10cd54dd86df6ef6 0xc10cd54dd86df6ef 0xf1dd35cc8fffffff 0x7f1dd35cc8ffffff

def z89 : W := mkw 0x1bed3eccdf45f756 0x81bed3eccdf45f75 0xfffd3fccffc7ffff 0xffffd3fccffc7fff

def z90 : W := mkw 0x4dbfc040edf6204a 0x04dbfc040edf6204 0xfffff1c0ffffe07f 0xffffff1c0ffffe07

def z91 : W := mkw 0x0040140002004404 0x0004014000200440 0x01c030008e00e000 0x401c030008e00e00

def z92 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x6000000001ff1ff8 0x16000000001ff1ff

def z93 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x1fdc31c000000000 0x41fdc31c00000000

def z94 : W := mkw 0x020428409040b042 0x0020428409040b04 0xbe1c39c0f040f87e 0xfbe1c39c0f040f87

def z95 : W := mkw 0x26563f70b268fd67 0x026563f70b268fd6 0xbe1e3ff0f078fffe 0xfbe1e3ff0f078fff

def z96 : W := mkw 0x0b643e40db40f546 0x00b643e40db40f54 0xfffc3fc0ffc0ffff 0xffffc3fc0ffc0fff

def z97 : W := mkw 0x82002b2200000000 0x082002b220000000 0x00000a3300000000 0x000000a330000000

def z98 : W := mkw 0x108d00cc84452252 0x8108d00cc8445225 0x901d01cc00470072 0x0901d01cc0047007

def z99 : W := mkw 0x0b206a15599b9bb0 0x40b206a15599b9bb 0xee23ce3f71ff1fff 0xbee23ce3f71ff1ff

def z100 : W := mkw 0x49a9c0004d960008 0x049a9c0004d96000 0x41e1c0000f870001 0x041e1c0000f87000

def z101 : W := mkw 0x8be9be8a5b00d504 0x08be9be8a5b00d50 0x6fe1fe0fff80ff8d 0xf6fe1fe0fff80ff8

def z102 : W := mkw 0x096016004b004504 0x0096016004b00450 0x41e006000f800781 0x041e006000f80078

def z103 : W := mkw 0x0000000049000000 0x0000000004900000 0x40000000ff800008 0x140000000ff80000

def z104 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x91dd31cc8e47e072 0x491dd31cc8e47e07

def z105 : W := mkw 0x8f72bf225b00d504 0x08f72bf225b00d50 0x6fe2fe33ff80ff8d 0xf6fe2fe33ff80ff8

def z106 : W := mkw 0x32cd3dfc964dfe77 0x832cd3dfc964dfe7 0xf1dd3dfc8e47fe7f 0x6f1dd3dfc8e47fe7

def z107 : W := mkw 0x00c9148c00010210 0x000c9148c0001021 0xf1dd35cc0047067f 0x6f1dd35cc0047067

def z108 : W := mkw 0x20040050fb68fd67 0x020040050fb68fd6 0x60000000fff8fff8 0x160000000fff8fff

def z109 : W := mkw 0x008d004084442042 0x0008d00408444204 0xf1dd31c08e47e07f 0x6f1dd31c08e47e07

def z110 : W := mkw 0x4d32800069200008 0x04d3280006920000 0x0e00000070000000 0x00e0000007000000

def z111 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x2fc03800fe00f80c 0xf2fc03800fe00f80

def z112 : W := mkw 0x449fc000a4f60008 0x0449fc000a4f6000 0x001fc000007f0002 0x0001fc000007f000

def z113 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x1ffc3fc000000005 0xe1ffc3fc00000000

def z114 : W := mkw 0x1004405586df6ef6 0xc1004405586df6ef 0x600000008ffffff8 0x1600000008ffffff

def z115 : W := mkw 0x10cd54dd86df6ef6 0xc10cd54dd86df6ef 0xf1ffffff8fffffff 0xff1ffffff8ffffff

def z116 : W := mkw 0x26166971b0fab8e3 0x426166971b0fab8e 0xbe3efbf3f1f8f9fe 0xfbe3efbf3f1f8f9f

def z117 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x6021c60f01ff1ff9 0x16021c60f01ff1ff

def z118 : W := mkw 0x12cd3ccc9645f656 0x812cd3ccc9645f65 0xffdd3dccfe47fe7f 0xfffdd3dccfe47fe7

def z119 : W := mkw 0x14df14cca6656656 0x814df14cca665665 0xffdf35ccfe7fe67f 0xfffdf35ccfe7fe67

def z120 : W := mkw 0x09a9800000000000 0x009a980000000000 0x01e1c00000000001 0x001e1c0000000000

def z121 : W := mkw 0x008d000484450210 0x0008d00048445021 0xe1dd040c8e47067f 0x6e1dd040c8e47067

def z122 : W := mkw 0x0040140002004404 0x0004014000200440 0x61e03e008f80ff8d 0xf61e03e008f80ff8

def z123 : W := mkw 0x4dffd600eff6450c 0x04dffd600eff6450 0x4fffc600ffff078b 0xf4fffc600ffff078

def z124 : W := mkw 0xa69fa9fab068b863 0x0a69fa9fab068b86 0xbe1ff9fff078f87e 0xfbe1ff9fff078f87

def z125 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x0fffc00000000003 0xe0fffc0000000000

def z126 : W := mkw 0x89e9968a4b004504 0x089e9968a4b00450 0x41e1c60f0f800781 0x041e1c60f0f80078

def z127 : W := mkw 0x8fffbfea80402042 0x08fffbfea8040204 0xbfffffff8040e07f 0xebfffffff8040e07

def z128 : W := mkw 0x2612293030289821 0x0261229303028982 0x9e1e39f070381806 0xf9e1e39f07038180

def z129 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x61c1040c8e47e679 0x061c1040c8e47e67

def z130 : W := mkw 0x8b603faa5b00d504 0x08b603faa5b00d50 0xffe03fffff80ff8d 0xfffe03fffff80ff8

def z131 : W := mkw 0x9fffbfeedf45f756 0x89fffbfeedf45f75 0xffffffffffc7ffff 0xfffffffffffc7fff

def z132 : W := mkw 0x59e9d48c4f97461c 0x859e9d48c4f97461 0x41e1c40c0f870601 0x041e1c40c0f87060

def z133 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xfe3e3ff0f1f8ffff 0xffe3e3ff0f1f8fff

def z134 : W := mkw 0x8f32ab2200000000 0x08f32ab220000000 0x0e22ca3300000000 0x80e22ca330000000

def z135 : W := mkw 0x89e9968a00000000 0x089e9968a0000000 0x01e1c60f00000001 0x001e1c60f0000000

def z136 : W := mkw 0x6f36e970f9fab86b 0x06f36e970f9fab86 0xbe3ef9f0f1f8f87e 0xfbe3ef9f0f1f8f87

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000e0000001f84 0x020000e0000001f8

def z138 : W := mkw 0x096056054b934794 0x4096056054b93479 0x41e1c60f0f870781 0x041e1c60f0f87078

def z139 : W := mkw 0x6fbfe975fdffbafb 0x46fbfe975fdffbaf 0xffffffffffffffff 0xffffffffffffffff

def z140 : W := mkw 0x19ed14cccf456656 0x819ed14cccf45665 0xfffd35ccffc7e67f 0xffffd35ccffc7e67

def z141 : W := mkw 0x449fc015a4ff0ab8 0x4449fc015a4ff0ab 0xe03fce3f01ff1fff 0xbe03fce3f01ff1ff

def z142 : W := mkw 0x0000000400010210 0x0000000040001021 0xe001040c0047067f 0x2e001040c0047067

def z143 : W := mkw 0x26166975b0fbbaf3 0x426166975b0fbbaf 0xfe3ffffff1ffffff 0xffe3ffffff1fffff

def z144 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fdc3fff00000004 0x49fdc3fff0000000

def z145 : W := mkw 0x0000000059009100 0x0000000005900910 0x0000000071801980 0x1000000007180198

def z146 : W := mkw 0x30040054b66dfe77 0x830040054b66dfe7 0x60000000fe7ffe78 0x160000000fe7ffe7

def z147 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x1ffdf7cf00000001 0x41ffdf7cf0000000

def z148 : W := mkw 0x4dbfc015edff0ab8 0x44dbfc015edff0ab 0xefffce3fffff1fff 0xfefffce3fffff1ff

def z149 : W := mkw 0x0612293000080820 0x0061229300008082 0xbe1e39f00078187e 0xfbe1e39f00078187

def z150 : W := mkw 0x20040050b068b863 0x020040050b068b86 0xa0020830f078f87e 0xba0020830f078f87

def z151 : W := mkw 0x2f763f60fb60f547 0x02f763f60fb60f54 0x1fdc31c0fe00e000 0x41fdc31c0fe00e00

def z152 : W := mkw 0x10cd14ccdf45f756 0x810cd14ccdf45f75 0xf1dd35ccffc7ffff 0x7f1dd35ccffc7fff

def z153 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xb1dc35cc8e00e674 0x4b1dc35cc8e00e67

def z154 : W := mkw 0x89e9d68f00930290 0x489e9d68f0093029 0x41e1c60f01870781 0x041e1c60f0187078

def z155 : W := mkw 0x2f763f70fb68fd67 0x02f763f70fb68fd6 0xfffe3ff0fff8ffff 0xffffe3ff0fff8fff

def z156 : W := mkw 0x8920820200000000 0x0892082020000000 0x0020c20300000000 0x00020c2030000000

def z157 : W := mkw 0x8be9bfaa00000000 0x08be9bfaa0000000 0x91e1ffff00000005 0x091e1ffff0000000

def z158 : W := mkw 0x4dbfc000fff6d50c 0x04dbfc000fff6d50 0x6fffc000ffffff8b 0xf6fffc000ffffff8

def z159 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0x4023ca3301ff198b 0xb4023ca3301ff198

def z160 : W := mkw 0x4d32c00069b20008 0x04d32c00069b2000 0x0e22c00071b80000 0x90e22c00071b8000

def z161 : W := mkw 0x8f32eb37009b0ab0 0x48f32eb37009b0ab 0xee23ce3f01ff1fff 0xbee23ce3f01ff1ff

def z162 : W := mkw 0x24160160a0602043 0x024160160a060204 0x101c01c000000000 0x0101c01c00000000

def z163 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe003c03f01ff1ffa 0x1e003c03f01ff1ff

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200e0000000005 0xa00200e000000000

def z165 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x1e1e39f0f038f800 0xd1e1e39f0f038f80

def z166 : W := mkw 0x1004004484452252 0x8100400448445225 0x0000000000470070 0x0000000000047007

def z167 : W := mkw 0x4ffffe00fff6d50c 0x04ffffe00fff6d50 0x6ffffe00ffffff8f 0xf6ffffe00ffffff8

def z168 : W := mkw 0x4dbbc0006db60008 0x04dbbc0006db6000 0x4fe3c0007fbf0001 0x94fe3c0007fbf000

def z169 : W := mkw 0x2f723f307b28dd25 0x02f723f307b28dd2 0x6fe23e30ffb8ff8d 0xf6fe23e30ffb8ff8

def z170 : W := mkw 0x02403e005b00d504 0x002403e005b00d50 0x60003e00ff80ff8c 0x160003e00ff80ff8

def z171 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020000001800009 0xb402000000180000

def z172 : W := mkw 0x0000400000920000 0x0000040000092000 0x4021c00001870001 0x04021c0000187000

def z173 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x0fdc000000000000 0x40fdc00000000000

def z174 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0xefe3fe3fff80ff8f 0xfefe3fe3fff80ff8

def z175 : W := mkw 0x000000004b004504 0x0000000004b00450 0x400000000f800780 0x0400000000f80078

def z176 : W := mkw 0x0ffbbe0000000000 0x00ffbbe000000000 0x0ffffe0000000007 0xe0ffffe000000000

def z177 : W := mkw 0x4d36c000edf60008 0x04d36c000edf6000 0x4e22c000ffff0008 0x94e22c000ffff000

def z178 : W := mkw 0x449fc015a4ff0ab8 0x4449fc015a4ff0ab 0x801fc03f007f0072 0x0801fc03f007f007

def z179 : W := mkw 0x0612292000000000 0x0061229200000000 0x9e1e39f000000006 0xe9e1e39f00000000

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x200030008000e00c 0x6200030008000e00

def z181 : W := mkw 0x000000005b00d504 0x0000000005b00d50 0x60000000ff80ff88 0x160000000ff80ff8

def z182 : W := mkw 0x4000400069b20008 0x04000400069b2000 0x0000000071b80000 0x10000000071b8000

def z183 : W := mkw 0xcfffffaaedf60008 0x0cfffffaaedf6000 0xdfffffffffff000f 0xfdfffffffffff000

def z184 : W := mkw 0x0b607e005b92d504 0x00b607e005b92d50 0x6fe3fe00ffffff8f 0xf6fe3fe00ffffff8

def z185 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fdff1ff00000002 0x49fdff1ff0000000

def z186 : W := mkw 0x02403e151209dfb4 0x402403e151209dfb 0xa0003e3f0000fff4 0x0a0003e3f0000fff

def z187 : W := mkw 0x0b607e155b9bdfb4 0x40b607e155b9bdfb 0xefe3fe3fffffffff 0xfefe3fe3ffffffff

def z188 : W := mkw 0x10cd54cc86d76656 0x810cd54cc86d7665 0xf1fff5cc8fffe67f 0xff1fff5cc8fffe67

def z189 : W := mkw 0x108d00cc84452252 0x8108d00cc8445225 0xd1dd01cc8e47007b 0x6d1dd01cc8e47007

def z190 : W := mkw 0x0004004080402042 0x0000400408040204 0x101c31c08000e000 0x4101c31c08000e00

def z191 : W := mkw 0x4d36c000e9f20008 0x04d36c000e9f2000 0x0e3ec000f1f8000a 0xf0e3ec000f1f8000

def z192 : W := mkw 0xc9e9d68a4d960008 0x0c9e9d68a4d96000 0x41e1c60f0f870001 0x041e1c60f0f87000

def z193 : W := mkw 0x34df15fca66d6e77 0x834df15fca66d6e7 0xf1df35fc8e7fe67f 0x6f1df35fc8e7fe67

def z194 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x9fffc1ff00000003 0xe9fffc1ff0000000

def z195 : W := mkw 0x02403c001200d404 0x002403c001200d40 0x6fc03c00fe00fe0d 0xf6fc03c00fe00fe0

def z196 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x8003c03f007f0072 0x08003c03f007f007

def z197 : W := mkw 0x0920020049000100 0x0092002004900010 0x0020020001800180 0x0002002000180018

def z198 : W := mkw 0x92cd3fee86456656 0x892cd3fee8645665 0xf1dd3fff8e47e67f 0x6f1dd3fff8e47e67

def z199 : W := mkw 0x8089808a00000000 0x08089808a0000000 0x0001c00f00000000 0x00001c00f0000000

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0x400100000047000b 0x2400100000047000

def z201 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x0fe03e0000000005 0xe0fe03e000000000

def z202 : W := mkw 0x9fffbfee86456656 0x89fffbfee8645665 0xffffffff8e47e67f 0xeffffffff8e47e67

def z203 : W := mkw 0x8f72bfaa00000000 0x08f72bfaa0000000 0x9e22ffff00000004 0x89e22ffff0000000

def z204 : W := mkw 0x00cd148884440000 0x000cd14888444000 0xd1dd35cc8e47000f 0x6d1dd35cc8e47000

def z205 : W := mkw 0xcfffbfaaed640008 0x0cfffbfaaed64000 0x1fdc31c0fe000000 0x41fdc31c0fe00000

def z206 : W := mkw 0x4dbf8000ed640008 0x04dbf8000ed64000 0x0fde0000fe78000a 0xf0fde0000fe78000

def z207 : W := mkw 0x4fbfe920edf60008 0x04fbfe920edf6000 0xdffff9f0ffff000f 0xfdffff9f0ffff000

def z208 : W := mkw 0xafffbfeab060b043 0x0afffbfeab060b04 0x1fdc31c0f000e000 0x41fdc31c0f000e00

def z209 : W := mkw 0x50cd54cceff7665e 0x850cd54cceff7665 0xf1dd35ccffffe67f 0x7f1dd35ccffffe67

def z210 : W := mkw 0x36df3decb665f657 0x836df3decb665f65 0xffdd35ccfe47e67f 0x6ffdd35ccfe47e67

def z211 : W := mkw 0x82403faa00000000 0x082403faa0000000 0x100031c000000000 0x0100031c00000000

def z212 : W := mkw 0x0b202a0059009100 0x00b202a005900910 0x0e200a0071801980 0x90e200a007180198

def z213 : W := mkw 0x84db95aa00000000 0x084db95aa0000000 0x91dff5ff00000007 0x691dff5ff0000000

def z214 : W := mkw 0x0920000000000000 0x0092000000000000 0x0fe0000000000001 0xe0fe000000000000

def z215 : W := mkw 0x1004405586df6ef6 0xc1004405586df6ef 0xe023ce3f8fffffff 0xbe023ce3f8ffffff

def z216 : W := mkw 0x4dbbc0004d960008 0x04dbbc0004d96000 0x4fffc0000f870003 0xe4fffc0000f87000

def z217 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe003c43f007f067f 0x2e003c43f007f067

def z218 : W := mkw 0x8ffbbfaa10009000 0x08ffbbfaa1000900 0xbffffffff000f80f 0xfbffffffff000f80

def z219 : W := mkw 0x4f32ea0079b29108 0x04f32ea0079b2910 0x0e22ca0071b81980 0x90e22ca0071b8198

def z220 : W := mkw 0x2f763f70b068b863 0x02f763f70b068b86 0xbffe3ff0f078f87f 0xfbffe3ff0f078f87

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x901c31c000000006 0x6901c31c00000000

def z222 : W := mkw 0x6f32e93079ba9829 0x06f32e93079ba982 0x0e22c83071b81800 0x90e22c83071b8180

def z223 : W := mkw 0x44164000edf60008 0x044164000edf6000 0x4e1e0000ffff000a 0xf4e1e0000ffff000

def z224 : W := mkw 0x8ffbffbf009b0ab0 0x48ffbffbf009b0ab 0x9fffffff007f0077 0xe9fffffff007f007

def z225 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0x9ffffffffe00e007 0xe9ffffffffe00e00

def z226 : W := mkw 0x9fffbfee86456656 0x89fffbfee8645665 0xffdd35cc8e47e67f 0x6ffdd35cc8e47e67

def z227 : W := mkw 0x0000400000920000 0x0000040000092000 0x6023ce0001ff1f8f 0xb6023ce0001ff1f8

def z228 : W := mkw 0x049f0000a4640000 0x0049f0000a464000 0x4fdf0000fe7f000b 0xf4fdf0000fe7f000

def z229 : W := mkw 0xbfffbffeb66dfe77 0x8bfffbffeb66dfe7 0xfffffffffe7ffe7f 0xffffffffffe7ffe7

def z230 : W := mkw 0x8fffbfaa84440000 0x08fffbfaa8444000 0xdfffffff8e47000f 0xedfffffff8e47000

def z231 : W := mkw 0x4dbfc011edfe08a8 0x44dbfc011edfe08a 0x4fffca33ffff198b 0xf4fffca33ffff198

def z232 : W := mkw 0x49a9c0054d970298 0x449a9c0054d97029 0x41e1c60f0f870781 0x041e1c60f0f87078

def z233 : W := mkw 0x6dbfc170edfe286b 0x06dbfc170edfe286 0xdfffc1f0ffff007b 0xfdfffc1f0ffff007

def z234 : W := mkw 0x02407e15129bdfb4 0x402407e15129bdfb 0xe023fe3f01ffffff 0xbe023fe3f01fffff

def z235 : W := mkw 0x049b800000000000 0x0049b80000000000 0x001fc00000000002 0x0001fc0000000000

def z236 : W := mkw 0x10c9548d06974694 0xc10c9548d0697469 0x41e1c60f0f870781 0x041e1c60f0f87078

def z237 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe3ffffff078f87f 0xfbe3ffffff078f87

def z238 : W := mkw 0x10cd14cc84452252 0x810cd14cc8445225 0x91dd35cc00470077 0x691dd35cc0047007

def z239 : W := mkw 0x26563d70b268fc67 0x026563d70b268fc6 0xffde3df0fe78fe7f 0xfffde3df0fe78fe7

def z240 : W := mkw 0xeffffffafdfeb86b 0x0effffffafdfeb86 0xfffffffffffff87f 0xffffffffffffff87

def z241 : W := mkw 0x4ffffe15ffffdfbc 0x44ffffe15ffffdfb 0xeffffe3fffffffff 0xfeffffe3ffffffff

def z242 : W := mkw 0x0b202a0059009100 0x00b202a005900910 0x0e00000070000000 0x00e0000007000000

def z243 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fc03000ff80ff88 0x56fc03000ff80ff8

def z244 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x60200e0001ff1ffd 0xb60200e0001ff1ff

def z245 : W := mkw 0x5dff94c8ef64644e 0x85dff94c8ef64644 0x1fdc31c0fe00e000 0x41fdc31c0fe00e00

def z246 : W := mkw 0x0b603e0010009000 0x00b603e001000900 0x2fe03e00f000f80d 0xf2fe03e00f000f80

def z247 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0fdfc000fe7f0002 0x40fdfc000fe7f000

def z248 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x51dd35cc8e07e601 0x451dd35cc8e07e60

def z249 : W := mkw 0x0040140002004404 0x0004014000200440 0x61c034008e00e60d 0x661c034008e00e60

def z250 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x4023ce3f01bf1f81 0x94023ce3f01bf1f8

def z251 : W := mkw 0x4f72fe007bb2d50c 0x04f72fe007bb2d50 0x6fe2fe00ffb8ff8d 0xf6fe2fe00ffb8ff8

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x0021c60f00000001 0x00021c60f0000000

def z253 : W := mkw 0x26162970a0682863 0x026162970a068286 0x9e1e39f000780076 0xe9e1e39f00078007

def z254 : W := mkw 0x0b603e001200d504 0x00b603e001200d50 0x2fe03e000000ff85 0xe2fe03e000000ff8

def z255 : W := mkw 0x0000400100920080 0x4000040010092008 0x0020c20301800180 0x00020c2030180018

def z256 : W := mkw 0x449fc000a4f60008 0x0449fc000a4f6000 0x41dfc0008e7f000b 0x641dfc0008e7f000

def z257 : W := mkw 0x108d40dd84df2af2 0xc108d40dd84df2af 0xf03fcfff01ff1fff 0xbf03fcfff01ff1ff

def z258 : W := mkw 0xcfffffaafff6d50c 0x0cfffffaafff6d50 0xffffffffffffff8f 0xfffffffffffffff8

def z259 : W := mkw 0x0b603e0002004404 0x00b603e000200440 0x6fe03e008e00e60d 0xe6fe03e008e00e60

def z260 : W := mkw 0x0b607e055b93d794 0x40b607e055b93d79 0x6fe1fe0fff87ff8d 0xf6fe1fe0fff87ff8

def z261 : W := mkw 0xafffbffab068b863 0x0afffbffab068b86 0xbffffffff078f87f 0xfbffffffff078f87

def z262 : W := mkw 0x800001aa00000000 0x0800001aa0000000 0x900001ff00000000 0x0900001ff0000000

def z263 : W := mkw 0x0b603e004b004504 0x00b603e004b00450 0x4fe03e000f800785 0xe4fe03e000f80078

def z264 : W := mkw 0x40044000a4f60008 0x040044000a4f6000 0x00000000007f0000 0x000000000007f000

def z265 : W := mkw 0x4089c00004960008 0x04089c0000496000 0x0001c00000070000 0x00001c0000007000

def z266 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe001040c01ff1fff 0x3e001040c01ff1ff

def z267 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fdd35cc00000007 0x69fdd35cc0000000

def z268 : W := mkw 0x220029701008b863 0x0220029701008b86 0xbe0039f0f000f87c 0xfbe0039f0f000f87

def z269 : W := mkw 0x49244000edf60008 0x049244000edf6000 0x4fe00000ffff0009 0xf4fe00000ffff000

def z270 : W := mkw 0x00c9148800000000 0x000c914880000000 0x01c1040c00000001 0x001c1040c0000000

def z271 : W := mkw 0xa49f81faa0682863 0x0a49f81faa068286 0x901fc1ff00780072 0x0901fc1ff0078007

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008000000180c 0xb200008000000180

def z273 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x8fe3fe3f00000007 0xe8fe3fe3f0000000

def z274 : W := mkw 0x104414cc86456656 0x8104414cc8645665 0xf00035cc8e47e67c 0x0f00035cc8e47e67

def z275 : W := mkw 0x2612292030209001 0x0261229203020900 0x0e00000070000000 0x00e0000007000000

def z276 : W := mkw 0x0b202a0059009100 0x00b202a005900910 0x6e200e0071801f8d 0xb6e200e0071801f8

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z278 : W := mkw 0x649fc170a4fe286b 0x0649fc170a4fe286 0x901fc1f0007f0072 0x0901fc1f0007f007

def z279 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1ffffff8e47e67f 0xef1ffffff8e47e67

def z280 : W := mkw 0x10c9148c06054614 0x810c9148c0605461 0x61c1340c8e07e60d 0x661c1340c8e07e60

def z281 : W := mkw 0x0000001400090a30 0x00000001400090a3 0xe0030c3c007f1e7f 0xbe0030c3c007f1e7

def z282 : W := mkw 0x16df3dec86456656 0x816df3dec8645665 0xffdf3dfc8e47e67f 0xeffdf3dfc8e47e67

def z283 : W := mkw 0x1040148c02014614 0x81040148c0201461 0x0000040c00000600 0x00000040c0000060

def z284 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe002083001ff1ffe 0xbe002083001ff1ff

def z285 : W := mkw 0x0000000400010210 0x0000000040001021 0x4001040c00070601 0x04001040c0007060

def z286 : W := mkw 0x1004004086446446 0x8100400408644644 0x000000008e00e000 0x0000000008e00e00

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003c03f00000002 0x08003c03f0000000

def z288 : W := mkw 0x0000400500930290 0x4000040050093029 0x4000000001870780 0x0400000000187078

def z289 : W := mkw 0x30cd14dcb66dfe77 0x830cd14dcb66dfe7 0xf1dd35ccfe7ffe7f 0x7f1dd35ccfe7ffe7

def z290 : W := mkw 0x20040050b068b863 0x020040050b068b86 0x20000000f078f878 0x120000000f078f87

def z291 : W := mkw 0x6fbfa970fd6cb86b 0x06fbfa970fd6cb86 0xbfde39f0fe78f87e 0xfbfde39f0fe78f87

def z292 : W := mkw 0xcfffbfaaed640008 0x0cfffbfaaed64000 0x9ffffffffe000007 0xe9ffffffffe00000

def z293 : W := mkw 0xafffbfeab060b043 0x0afffbfeab060b04 0x9ffffffff000e007 0xe9ffffffff000e00

def z294 : W := mkw 0xafffbffab068b863 0x0afffbffab068b86 0xbfde39f0f078f87e 0xfbfde39f0f078f87

def z295 : W := mkw 0x36df3de8b664f447 0x836df3de8b664f44 0x1fdc31c0fe00e000 0x41fdc31c0fe00e00

def z296 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x3e1c31c0f078f878 0x53e1c31c0f078f87

def z297 : W := mkw 0x108d00cc86456656 0x8108d00cc8645665 0xf01d01cc8e47e67a 0x0f01d01cc8e47e67

def z298 : W := mkw 0x4d32c01569bb0ab8 0x44d32c01569bb0ab 0xee23ce3f71ff1fff 0xbee23ce3f71ff1ff

def z299 : W := mkw 0x5dbfc044eff7665e 0x85dbfc044eff7665 0x6fffc000ffffe67b 0xf6fffc000ffffe67

def z300 : W := mkw 0x004014005b00d504 0x0004014005b00d50 0x61c03400ff80ff8d 0x761c03400ff80ff8

def z301 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0x8000003f00000070 0x08000003f0000007

def z302 : W := mkw 0x00c9148800000000 0x000c914880000000 0x91ffffff00000007 0xe91ffffff0000000

def z303 : W := mkw 0x24164175a0fb2af3 0x424164175a0fb2af 0x901fc1ff007f0072 0x0901fc1ff007f007

def z304 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xcfffce3fffff000f 0xfcfffce3fffff000

def z305 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x101c01c000000000 0x0101c01c00000000

def z306 : W := mkw 0x2612293030289821 0x0261229303028982 0x0e02083070381800 0x90e0208307038180

def z307 : W := mkw 0x0040140000000000 0x0004014000000000 0x01c0340000000005 0x601c034000000000

def z308 : W := mkw 0x0000000010009000 0x0000000001000900 0x20000000f000f808 0x120000000f000f80

def z309 : W := mkw 0x24160170a0682863 0x024160170a068286 0x901e01f000780072 0x0901e01f00078007

def z310 : W := mkw 0x26162930b0689821 0x026162930b068982 0x0e1e0830f078180a 0xf0e1e0830f078180

def z311 : W := mkw 0x2b643e50fb68fd67 0x02b643e50fb68fd6 0x6fe03e00fff8fffd 0xf6fe03e00fff8fff

def z312 : W := mkw 0x0920400049920000 0x0092040004992000 0x4fe3c000ffff000b 0xf4fe3c000ffff000

def z313 : W := mkw 0x0b603e045b01d714 0x00b603e045b01d71 0xefe13e0cffc7ffff 0xfefe13e0cffc7fff

def z314 : W := mkw 0x5dffd4c8eff6644e 0x85dffd4c8eff6644 0x5ffff1c0ffffe00b 0xf5ffff1c0ffffe00

def z315 : W := mkw 0x0be93e8800000000 0x00be93e880000000 0x9ffd3fcc00000007 0xe9ffd3fcc0000000

def z316 : W := mkw 0x8ffbbfaa59009100 0x08ffbbfaa5900910 0x9fffffff71801987 0xf9fffffff7180198

def z317 : W := mkw 0x0dbb800049000000 0x00dbb80004900000 0x4fffc000ff80000b 0xf4fffc000ff80000

def z318 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1fd3fcc8fc7ffff 0xff1fd3fcc8fc7fff

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200a0001801980 0x900200a000180198

def z320 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x41ffc0000fff0003 0x041ffc0000fff000

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0xe023ce3f01801f8f 0xbe023ce3f01801f8

def z322 : W := mkw 0x0004004080402042 0x0000400408040204 0x901c01c000400072 0x0901c01c00040007

def z323 : W := mkw 0xcfbfeb22edf60008 0x0cfbfeb22edf6000 0x4fffca33ffff000b 0xf4fffca33ffff000

def z324 : W := mkw 0x10c914cc06056656 0x810c914cc0605665 0xf1c135cc0e07e675 0x0f1c135cc0e07e67

def z325 : W := mkw 0xa6563ffab068b863 0x0a6563ffab068b86 0xbe1e3ffff078f87e 0xfbe1e3ffff078f87

def z326 : W := mkw 0x10040044df45f756 0x810040044df45f75 0x60000000ffc7fff8 0x160000000ffc7fff

def z327 : W := mkw 0x108d00c884442042 0x8108d00c88444204 0x101c01c000000000 0x0101c01c00000000

def z328 : W := mkw 0x2f763f60fb60f547 0x02f763f60fb60f54 0x7ffc3fc0ff80ff8d 0xf7ffc3fc0ff80ff8

def z329 : W := mkw 0x449fc000edf60008 0x0449fc000edf6000 0x401fc000ffff000a 0x1401fc000ffff000

def z330 : W := mkw 0x2b603f705b08fd67 0x02b603f705b08fd6 0xffe03ff0ff80fffd 0xfffe03ff0ff80fff

def z331 : W := mkw 0x2f767f75fbfbfff7 0x42f767f75fbfbfff 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x0000000002004404 0x0000000000200440 0x600000008e00e608 0x0600000008e00e60

def z333 : W := mkw 0x49a9c0004d960008 0x049a9c0004d96000 0x4fe1c000ff870009 0xf4fe1c000ff87000

def z334 : W := mkw 0x32403dfc1209fe77 0x832403dfc1209fe7 0xb0003dfc0000fe74 0x0b0003dfc0000fe7

def z335 : W := mkw 0x26162975b069baf3 0x426162975b069baf 0xbe1e3ffff078fffe 0xfbe1e3ffff078fff

def z336 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xa022ce3f01b81ff4 0x9a022ce3f01b81ff

def z337 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x4fe03600ff80e781 0x44fe03600ff80e78

def z338 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0x7ffc3fc0ff80ff8d 0xf7ffc3fc0ff80ff8

def z339 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0xe0200e3f01801ffd 0xbe0200e3f01801ff

def z340 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe021ce3f01871ff5 0x0e021ce3f01871ff

def z341 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x0fc0300000000000 0x40fc030000000000

def z342 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x4fe00e007f801f81 0x94fe00e007f801f8

def z343 : W := mkw 0x1b643e44df45f756 0x81b643e44df45f75 0x6fe03e00ffc7fffd 0xf6fe03e00ffc7fff

def z344 : W := mkw 0x0920000049000000 0x0092000004900000 0x0e20000071800000 0x90e2000007180000

def z345 : W := mkw 0x008d400084d60000 0x0008d400084d6000 0x41ffc0008fff000b 0xf41ffc0008fff000

def z346 : W := mkw 0x8ffbffbb009a08a0 0x48ffbffbb009a08a 0x9fffffff01b81987 0xf9fffffff01b8198

def z347 : W := mkw 0x24160170b068b863 0x024160170b068b86 0xb01e01f0f078f87a 0x1b01e01f0f078f87

def z348 : W := mkw 0x99ed96ce86456656 0x899ed96ce8645665 0xf1fdf7cf8e47e67f 0x6f1fdf7cf8e47e67

def z349 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0x2000000000001ff0 0x02000000000001ff

def z350 : W := mkw 0x4fbfea00fdf69108 0x04fbfea00fdf6910 0x4fffca00ffff198b 0xf4fffca00ffff198

def z351 : W := mkw 0x6fbfe930fdfe9829 0x06fbfe930fdfe982 0x4fffc830ffff180b 0xf4fffc830ffff180

def z352 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0x8023ce3f01b81987 0xb8023ce3f01b8198

def z353 : W := mkw 0x0920000049000000 0x0092000004900000 0x41e000000f800001 0x041e000000f80000

def z354 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xb01d35cc0047e676 0x0b01d35cc0047e67

def z355 : W := mkw 0x8fffbfaaa0600000 0x08fffbfaaa060000 0x9ffffffff078000f 0xf9ffffffff078000

def z356 : W := mkw 0x04164000a0f20000 0x004164000a0f2000 0x4e3fc000f1ff000b 0xf4e3fc000f1ff000

def z357 : W := mkw 0x02403e001200d504 0x002403e001200d50 0x000030000000e000 0x0000030000000e00

def z358 : W := mkw 0x4dbfc005edf70298 0x44dbfc005edf7029 0x4fffc60fffff078b 0xf4fffc60fffff078

def z359 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xa003ce3f007f1ff6 0x0a003ce3f007f1ff

def z360 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0xa0020e3f00781ffe 0xba0020e3f00781ff

def z361 : W := mkw 0x04160000a0600000 0x004160000a060000 0x001e000000780002 0x0001e00000078000

def z362 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0xe0010e3f00471fff 0x2e0010e3f00471ff

def z363 : W := mkw 0x0000000500010290 0x4000000050001029 0x0000060f00000780 0x00000060f0000078

def z364 : W := mkw 0x8ffbffaf00930290 0x48ffbffaf0093029 0xdfffffff01870787 0xedfffffff0187078

def z365 : W := mkw 0x20040040b060b043 0x020040040b060b04 0x00000000f000e000 0x000000000f000e00

def z366 : W := mkw 0x8ffbbfaa1200d504 0x08ffbbfaa1200d50 0xbfffffff0000ff87 0xebfffffff0000ff8

def z367 : W := mkw 0x000000001200d504 0x0000000001200d50 0x200000000000ff80 0x0200000000000ff8

def z368 : W := mkw 0x1bed3ecc86456656 0x81bed3ecc8645665 0xfffd3fcc8e47e67f 0xefffd3fcc8e47e67

def z369 : W := mkw 0x0000000400010210 0x0000000040001021 0xa000040c00000674 0x0a000040c0000067

def z370 : W := mkw 0x82403fbf00090ab0 0x482403fbf00090ab 0xb0003fff00001ff4 0x0b0003fff00001ff

def z371 : W := mkw 0x1004004486456656 0x8100400448645665 0xe001040c8e47e67f 0x2e001040c8e47e67

def z372 : W := mkw 0x0412000000000000 0x0041200000000000 0x0e1e000000000002 0xe0e1e00000000000

def z373 : W := mkw 0x59edd4cccfd7665e 0x859edd4cccfd7665 0xf1fdf5cc8fc7e67f 0x6f1fdf5cc8fc7e67

def z374 : W := mkw 0x12cd3ecc9645f756 0x812cd3ecc9645f75 0xf1dd3fcc8e47ffff 0x6f1dd3fcc8e47fff

def z375 : W := mkw 0x99e9968e06054614 0x899e9968e0605461 0x41e1c60f0e070601 0x041e1c60f0e07060

def z376 : W := mkw 0x200000501008b863 0x0200000501008b86 0x200000000000f870 0x0200000000000f87

def z377 : W := mkw 0x0616296080402042 0x0061629608040204 0xbe1e39f08040e07e 0xebe1e39f08040e07

def z378 : W := mkw 0x0000001000080820 0x0000000100008082 0x8002003000780072 0x0800200300078007

def z379 : W := mkw 0x0089008800000000 0x0008900880000000 0x901d01cc00000002 0x0901d01cc0000000

def z380 : W := mkw 0x0000400000920000 0x0000040000092000 0x4000000001ff0008 0x14000000001ff000

def z381 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xc023c03f01ff007b 0xbc023c03f01ff007

def z382 : W := mkw 0x36162974b66dfe77 0x836162974b66dfe7 0xfe1e39f0fe7ffe7e 0xffe1e39f0fe7ffe7

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001040c00000007 0x28001040c0000000

def z384 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x2e203e007180ff84 0x92e203e007180ff8

def z385 : W := mkw 0x04160040a0602042 0x004160040a060204 0xbe1e31c0f078e07e 0xfbe1e31c0f078e07

def z386 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xffffffff01801f8f 0xfffffffff01801f8

def z387 : W := mkw 0x8ffbbfae00010210 0x08ffbbfae0001021 0xffffffff0047067f 0xeffffffff0047067

def z388 : W := mkw 0x9fffbfea86446446 0x89fffbfea8644644 0x9fffffff8e00e007 0xe9fffffff8e00e00

def z389 : W := mkw 0x02403e001200d504 0x002403e001200d50 0x60203e000180ff8d 0xb60203e000180ff8

def z390 : W := mkw 0x4d32c01169ba08a8 0x44d32c01169ba08a 0x0e22ca3371b81980 0x90e22ca3371b8198

def z391 : W := mkw 0x19ed16cccf456756 0x819ed16cccf45675 0xf1fd37cc8fc7e7ff 0x6f1fd37cc8fc7e7f

def z392 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x61e03e000f80ff85 0x061e03e000f80ff8

def z393 : W := mkw 0x5ffffeccfff7f75e 0x85ffffeccfff7f75 0xffffffccffffffff 0xfffffffccfffffff

def z394 : W := mkw 0x7ffffdfcfffffe7f 0x87ffffdfcfffffe7 0xfffffdfcfffffe7f 0xffffffdfcfffffe7

def z395 : W := mkw 0x0b607e115b9adda4 0x40b607e115b9adda 0x6fe2fe33ffb8ff8d 0xf6fe2fe33ffb8ff8

def z396 : W := mkw 0x8412812200000000 0x0841281220000000 0x0002c03300000000 0x00002c0330000000

def z397 : W := mkw 0x1bed3eccdf45f756 0x81bed3eccdf45f75 0xffdd35ccfe47e67f 0x6ffdd35ccfe47e67

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002083000000006 0xa800208300000000

def z399 : W := mkw 0x8f32eb33009a08a0 0x48f32eb33009a08a 0x0e22ca3301b81980 0x90e22ca3301b8198

def z400 : W := mkw 0x0040140002004404 0x0004014000200440 0x41c004000e000601 0x041c004000e00060

def z401 : W := mkw 0x00c9549d009b0ab0 0x400c9549d009b0ab 0xf1ffffff01ff1fff 0xff1ffffff01ff1ff

def z402 : W := mkw 0x0fbba92000000000 0x00fbba9200000000 0x9ffff9f000000007 0xe9ffff9f00000000

def z403 : W := mkw 0x4dffd400eff6440c 0x04dffd400eff6440 0x6ffff400ffffe60f 0xf6ffff400ffffe60

def z404 : W := mkw 0x0000001000080820 0x0000000100008082 0xe0220e3001f81fff 0xbe0220e3001f81ff

def z405 : W := mkw 0x096056154b9b4fb4 0x4096056154b9b4fb 0xe1e3ce3f0fff1fff 0xbe1e3ce3f0fff1ff

def z406 : W := mkw 0x1044144486456656 0x8104414448645665 0x61c034008e47e67d 0x661c034008e47e67

def z407 : W := mkw 0x0004000080400000 0x0000400008040000 0x001c00008040000a 0x6001c00008040000

def z408 : W := mkw 0x26df3df8b068b863 0x026df3df8b068b86 0xbfdf3dfcf078f87f 0xfbfdf3dfcf078f87

def z409 : W := mkw 0x108d00cc84452252 0x8108d00cc8445225 0xf01d05cc0047067f 0x2f01d05cc0047067

def z410 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1c39f0f000f874 0x4be1c39f0f000f87

def z411 : W := mkw 0x2000017000082863 0x0200001700008286 0x900001f000000070 0x0900001f00000007

def z412 : W := mkw 0x008d401584df0ab0 0x4008d401584df0ab 0xe1ffce3f8fff1fff 0xfe1ffce3f8fff1ff

def z413 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fc03400fe00e60d 0x66fc03400fe00e60

def z414 : W := mkw 0x949f81ee84452252 0x8949f81ee8445225 0x901fc1ff00470072 0x0901fc1ff0047007

def z415 : W := mkw 0x0000004000002042 0x0000000400000204 0xb00031c00000e074 0x0b00031c00000e07

def z416 : W := mkw 0x02002a0010009100 0x002002a001000910 0x00000a0000001980 0x000000a000000198

def z417 : W := mkw 0x36563dfcb269fe77 0x836563dfcb269fe7 0xbe1e3dfcf078fe7e 0xfbe1e3dfcf078fe7

def z418 : W := mkw 0x04164015a0fb0ab0 0x404164015a0fb0ab 0xee3fce3ff1ff1fff 0xfee3fce3ff1ff1ff

def z419 : W := mkw 0x220029601000b043 0x0220029601000b04 0x100031c00000e000 0x0100031c00000e00

def z420 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x6023c00001ff1ffb 0xb6023c00001ff1ff

def z421 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x4fe03000ff80e009 0xf4fe03000ff80e00

def z422 : W := mkw 0x8ffbbfbf00090ab0 0x48ffbbfbf00090ab 0xbfffffff00001ff7 0xebfffffff00001ff

def z423 : W := mkw 0x104014cc02016656 0x8104014cc0201665 0xf1c035cc8e00e67d 0x6f1c035cc8e00e67

def z424 : W := mkw 0x4dbf8000ed640008 0x04dbf8000ed64000 0x4fdd0000fe47000b 0x64fdd0000fe47000

def z425 : W := mkw 0x1b603ecc5b01f756 0x81b603ecc5b01f75 0xffe03fccff80fffd 0xfffe03fccff80fff

def z426 : W := mkw 0x22042970b068b863 0x022042970b068b86 0xb00039f0f078f87c 0x1b00039f0f078f87

def z427 : W := mkw 0x40040000ed640008 0x040040000ed64000 0x00000000fe000000 0x000000000fe00000

def z428 : W := mkw 0x8ffbbfaa49000000 0x08ffbbfaa4900000 0xdfffffffff80000f 0xfdfffffffff80000

def z429 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x00000000007f0070 0x000000000007f007

def z430 : W := mkw 0x0040160002004504 0x0004016000200450 0x0000060000000780 0x0000006000000078

def z431 : W := mkw 0x0000400500930290 0x4000040050093029 0x4023c60f01ff078b 0xb4023c60f01ff078

def z432 : W := mkw 0x49adc000edf60008 0x049adc000edf6000 0x41e1c000ffff0009 0x141e1c000ffff000

def z433 : W := mkw 0x82407fbf009b0ab0 0x482407fbf009b0ab 0xf023ffff01ff1fff 0xbf023ffff01ff1ff

def z434 : W := mkw 0x8ffbffbf5b9bdfb4 0x48ffbffbf5b9bdfb 0xffffffffffffffff 0xffffffffffffffff

def z435 : W := mkw 0x0000001000080820 0x0000000100008082 0x2000000000781878 0x1200000000078187

def z436 : W := mkw 0x008d000084440000 0x0008d00008444000 0x001d000000470002 0x0001d00000047000

def z437 : W := mkw 0x02006815109b9ab0 0x402006815109b9ab 0xee23fe3ff1ffffff 0xfee23fe3ff1fffff

def z438 : W := mkw 0x82403faa1200d504 0x082403faa1200d50 0xb0003fff0000ff84 0x0b0003fff0000ff8

def z439 : W := mkw 0x000040155b9bdfb4 0x4000040155b9bdfb 0xe023ce3fffffffff 0xbe023ce3ffffffff

def z440 : W := mkw 0x0004005080482862 0x0000400508048286 0xb01e39f08078f87e 0xfb01e39f08078f87

def z441 : W := mkw 0x0000400400930210 0x0000040040093021 0xe023c40c01ff067f 0xbe023c40c01ff067

def z442 : W := mkw 0x1000004402016656 0x8100000440201665 0x200000000000e670 0x0200000000000e67

def z443 : W := mkw 0x82c93faa00000000 0x082c93faa0000000 0x91dd3fff00000007 0x691dd3fff0000000

def z444 : W := mkw 0xcffbffaa4d960008 0x0cffbffaa4d96000 0xdfffffff0f870007 0xedfffffff0f87000

def z445 : W := mkw 0x10c9549d069f4eb4 0xc10c9549d069f4eb 0xe1e3ce3f0fff1fff 0xbe1e3ce3f0fff1ff

def z446 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x2e020830f078f878 0x92e020830f078f87

def z447 : W := mkw 0xcf32eb2269b20008 0x0cf32eb2269b2000 0x0e22ca3371b80000 0x90e22ca3371b8000

def z448 : W := mkw 0x0b603e105b08dd24 0x00b603e105b08dd2 0xefe23e30fff8ffff 0xfefe23e30fff8fff

def z449 : W := mkw 0x0960160000000000 0x0096016000000000 0x01e0060000000001 0x001e006000000000

def z450 : W := mkw 0x104414cc82416656 0x8104414cc8241665 0xb01c35cc8040e67e 0x6b01c35cc8040e67

def z451 : W := mkw 0x0040140402014614 0x0004014040201461 0xe1c1340c8e47e67f 0x6e1c1340c8e47e67

def z452 : W := mkw 0x20044055b0fbbaf3 0x420044055b0fbbaf 0x60000000f1fffff8 0x160000000f1fffff

def z453 : W := mkw 0x104054dd029b6ef6 0xc104054dd029b6ef 0xf023ffff01ffffff 0xbf023ffff01fffff

def z454 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0ffec000ffb80000 0xd0ffec000ffb8000

def z455 : W := mkw 0x36df7dfdb6fffef7 0xc36df7dfdb6fffef 0xffffffffffffffff 0xffffffffffffffff

def z456 : W := mkw 0x0004000084440000 0x0000400008444000 0x400000008e470008 0x0400000008e47000

def z457 : W := mkw 0x0be93e885b00d504 0x00be93e885b00d50 0xfffd3fccff80ff8f 0xffffd3fccff80ff8

def z458 : W := mkw 0x5dffd4ddefff6efe 0xc5dffd4ddefff6ef 0xffffffffffffffff 0xffffffffffffffff

def z459 : W := mkw 0x6fbfa960fd64b04b 0x06fbfa960fd64b04 0x1fdc31c0fe00e000 0x41fdc31c0fe00e00

def z460 : W := mkw 0x261229703028b863 0x0261229703028b86 0xbe0239f07038f874 0x9be0239f07038f87

def z461 : W := mkw 0x408d4000edf60008 0x0408d4000edf6000 0x41dd0000ffff000b 0x741dd0000ffff000

def z462 : W := mkw 0x020028005b00d504 0x0020028005b00d50 0x6e003800ff80ff8c 0xf6e003800ff80ff8

def z463 : W := mkw 0x1bed3ec8df44f546 0x81bed3ec8df44f54 0x1fdc31c0fe00e000 0x41fdc31c0fe00e00

def z464 : W := mkw 0x86523faa00000000 0x086523faa0000000 0x9e1e3fff00000006 0xe9e1e3fff0000000

def z465 : W := mkw 0x0612292000000000 0x0061229200000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z466 : W := mkw 0xa2403ffa1008b863 0x0a2403ffa1008b86 0xb0003fff0000f874 0x0b0003fff0000f87

def z467 : W := mkw 0x82403faa00000000 0x082403faa0000000 0x9023ffff00000007 0xa9023ffff0000000

def z468 : W := mkw 0x0200280000000000 0x0020028000000000 0x0e00380000000004 0xe0e0038000000000

def z469 : W := mkw 0x0dbbc00000920000 0x00dbbc0000092000 0x4fffc00001ff000b 0xf4fffc00001ff000

def z470 : W := mkw 0x0b202a0059009100 0x00b202a005900910 0x4fe00a00ff801989 0xf4fe00a00ff80198

def z471 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0x0002c03300380000 0x00002c0330038000

def z472 : W := mkw 0x89e9968a00000000 0x089e9968a0000000 0x01c0000000000000 0x001c000000000000

def z473 : W := mkw 0x8ffbffaa00920000 0x08ffbffaa0092000 0xdfffffff01ff000f 0xfdfffffff01ff000

def z474 : W := mkw 0x108d004486456656 0x8108d00448645665 0x61dd00008e47e67b 0x661dd00008e47e67

def z475 : W := mkw 0x4dbfc015edff0ab8 0x44dbfc015edff0ab 0x6fffc000ffff1ffb 0xf6fffc000ffff1ff

def z476 : W := mkw 0x24160170a0682863 0x024160170a068286 0xb01e31f08078e07e 0x6b01e31f08078e07

def z477 : W := mkw 0x108d00cc84452252 0x8108d00cc8445225 0xb01d31cc8047e07e 0x6b01d31cc8047e07

def z478 : W := mkw 0x096016004b004504 0x0096016004b00450 0x4fe00600ff800789 0xf4fe00600ff80078

def z479 : W := mkw 0x10c914cc02016656 0x810c914cc0201665 0xb1dd35cc0000e677 0x6b1dd35cc0000e67

def z480 : W := mkw 0x09ad0000cd440000 0x009ad0000cd44000 0x4ffd0000ffc7000b 0xf4ffd0000ffc7000

def z481 : W := mkw 0xaffbbffa1008b863 0x0affbbffa1008b86 0xbfffffff0000f877 0xebfffffff0000f87

def z482 : W := mkw 0x0b206a11599a99a0 0x40b206a11599a99a 0x0e22ca3371b81980 0x90e22ca3371b8198

def z483 : W := mkw 0x49a9c0004d960008 0x049a9c0004d96000 0x41e3c0000fff000b 0xb41e3c0000fff000

def z484 : W := mkw 0x92403fee02016656 0x892403fee0201665 0xb0003fff0000e674 0x0b0003fff0000e67

def z485 : W := mkw 0x000000005b00d504 0x0000000005b00d50 0x00000000fe00e000 0x000000000fe00e00

def z486 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x1ffefbf300000000 0xc1ffefbf30000000

def z487 : W := mkw 0x10c9148806044404 0x810c914880604440 0x01c000000e000000 0x001c000000e00000

def z488 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x8023ca3f01ff19f2 0x98023ca3f01ff19f

def z489 : W := mkw 0xafffbffaa0682863 0x0afffbffaa068286 0x9fffffff00780077 0xe9fffffff0078007

def z490 : W := mkw 0x0089000000000000 0x0008900000000000 0x01dd000000000003 0x601dd00000000000

def z491 : W := mkw 0x06126935009b0ab0 0x406126935009b0ab 0xfe3fffff01ff1fff 0xffe3fffff01ff1ff

def z492 : W := mkw 0xc49fc1aaa4f60008 0x0c49fc1aaa4f6000 0x901fc1ff007f0002 0x0901fc1ff007f000

def z493 : W := mkw 0x00c9148800000000 0x000c914880000000 0x11dc31c000000000 0x411dc31c00000000

def z494 : W := mkw 0x0000400500930290 0x4000040050093029 0xe021c60f01c707ff 0x2e021c60f01c707f

def z495 : W := mkw 0x0ffbbe005b00d504 0x00ffbbe005b00d50 0x6ffffe00ff80ff8f 0xf6ffffe00ff80ff8

def z496 : W := mkw 0x0b603e155b09dfb4 0x40b603e155b09dfb 0xefe03e3fff80fffd 0xfefe03e3fff80fff

def z497 : W := mkw 0x1089008c04050210 0x81089008c0405021 0x0001000c00070000 0x00001000c0007000

def z498 : W := mkw 0x104014c802006446 0x8104014c80200644 0x100031c00000e000 0x0100031c00000e00

def z499 : W := mkw 0x4920c00049920008 0x04920c0004992000 0x0020c00001800000 0x00020c0000180000

def z500 : W := mkw 0x096016004b004504 0x0096016004b00450 0x01c000000e000000 0x001c000000e00000

def z501 : W := mkw 0x0004004480412252 0x0000400448041225 0xf01d35cc8047e67f 0x6f01d35cc8047e67

def z502 : W := mkw 0x00040000a0600000 0x000040000a060000 0x00000000f0780008 0x100000000f078000

def z503 : W := mkw 0x10cd148c86454614 0x810cd148c8645461 0x41dd040c8e47060b 0x641dd040c8e47060

def z504 : W := mkw 0x2fbfa970b068b863 0x02fbfa970b068b86 0xbffff9f0f078f87f 0xfbffff9f0f078f87

def z505 : W := mkw 0x4dbfc015edff0ab8 0x44dbfc015edff0ab 0xcfffc03fffff007b 0xfcfffc03fffff007

def z506 : W := mkw 0x008d000084440000 0x0008d00008444000 0x01dc00008e000000 0x401dc00008e00000

def z507 : W := mkw 0x8fbbab2200000000 0x08fbbab220000000 0x0fffca3300000003 0xe0fffca330000000

def z508 : W := mkw 0x0000000400010210 0x0000000040001021 0xe023ce3f0047067f 0xae023ce3f0047067

def z509 : W := mkw 0x26166970b0fab863 0x026166970b0fab86 0xfe3ff9f0f1fff87f 0xffe3ff9f0f1fff87

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x0023c00000000003 0xa0023c0000000000

def z511 : W := mkw 0x10cd14c886446446 0x810cd14c88644644 0x91dd35cc8e00e007 0x691dd35cc8e00e00

def z512 : W := mkw 0xcfffffaaedf60008 0x0cfffffaaedf6000 0x5ffff1c0ffff000b 0xf5ffff1c0ffff000

def z513 : W := mkw 0x22403f701208fd67 0x022403f701208fd6 0xb0003ff00000fff4 0x0b0003ff00000fff

def z514 : W := mkw 0x40044000fff6d50c 0x040044000fff6d50 0x60000000ffffff88 0x160000000ffffff8

def z515 : W := mkw 0x9ffbbfee02016656 0x89ffbbfee0201665 0xbfffffff0000e677 0xebfffffff0000e67

def z516 : W := mkw 0x0dbf8000a0600000 0x00dbf8000a060000 0x0fffc000f078000b 0xf0fffc000f078000

def z517 : W := mkw 0x10cd54dd86df6ef6 0xc10cd54dd86df6ef 0xf1dff5ff8e7fe67f 0x6f1dff5ff8e7fe67

def z518 : W := mkw 0x04160000a0600000 0x004160000a060000 0x0e1c0000f0000000 0x40e1c0000f000000

def z519 : W := mkw 0x4b647e00fff6d50c 0x04b647e00fff6d50 0x6fe03e00ffffff8d 0xf6fe03e00ffffff8

def z520 : W := mkw 0x66166970fdfeb86b 0x066166970fdfeb86 0xfe1e39f0fffff87e 0xffe1e39f0fffff87

def z521 : W := mkw 0x0920000049000000 0x0092000004900000 0x0fc00000fe000000 0x40fc00000fe00000

def z522 : W := mkw 0x26162960b060b043 0x026162960b060b04 0x9e1e39f0f000e006 0xe9e1e39f0f000e00

def z523 : W := mkw 0x4be9fe005f96d50c 0x04be9fe005f96d50 0x6fe1fe00ff87ff8d 0xf6fe1fe00ff87ff8

def z524 : W := mkw 0x49a980004d040008 0x049a980004d04000 0x01c000000e000000 0x001c000000e00000

def z525 : W := mkw 0x369f29fcb46dba73 0x8369f29fcb46dba7 0xbe1f39fcf07ff87e 0xfbe1f39fcf07ff87

def z526 : W := mkw 0x000000005b00d504 0x0000000005b00d50 0x60200e00ff80ff8d 0xb60200e00ff80ff8

def z527 : W := mkw 0x00cd14c880402042 0x000cd14c88040204 0xb1dd35cc8040e07f 0x6b1dd35cc8040e07

def z528 : W := mkw 0x0000000400010210 0x0000000040001021 0x8001000c00470072 0x08001000c0047007

def z529 : W := mkw 0x0000001000080820 0x0000000100008082 0x0002083000381800 0x9000208300038180

def z530 : W := mkw 0x261229701008b863 0x0261229701008b86 0xbe1e39f00000f876 0xebe1e39f00000f87

def z531 : W := mkw 0x86dbbfaa00000000 0x086dbbfaa0000000 0x901fffff00000006 0x0901fffff0000000

def z532 : W := mkw 0x06db3da800000000 0x006db3da80000000 0x9fdf3dfc00000007 0xe9fdf3dfc0000000

def z533 : W := mkw 0x096016004b004504 0x0096016004b00450 0x61e036008f80e78d 0x661e036008f80e78

def z534 : W := mkw 0x20040050b068b863 0x020040050b068b86 0xb01c31c0f078f87e 0x7b01c31c0f078f87

def z535 : W := mkw 0x400040004d960008 0x0400040004d96000 0x400000000f870000 0x0400000000f87000

def z536 : W := mkw 0x8ffbbfba00080820 0x08ffbbfba0008082 0xbfffffff0078187f 0xfbfffffff0078187

def z537 : W := mkw 0x096016004b004504 0x0096016004b00450 0x61e00e000f801f8d 0xb61e00e000f801f8

def z538 : W := mkw 0x0b603e0000000000 0x00b603e000000000 0x6fe03e0001801f8d 0xf6fe03e0001801f8

def z539 : W := mkw 0x269f2970b46cb863 0x0269f2970b46cb86 0xffdf39f0fe7ff87f 0xfffdf39f0fe7ff87

def z540 : W := mkw 0x0200280010009000 0x0020028001000900 0x0e003000f000e000 0x40e003000f000e00

def z541 : W := mkw 0xcffbffaa69b20008 0x0cffbffaa69b2000 0x9fffffff71b80007 0xf9fffffff71b8000

def z542 : W := mkw 0x0200280010009000 0x0020028001000900 0x0e00080070001800 0x90e0008007000180

def z543 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x8023ce3f007f0077 0xa8023ce3f007f007

def z544 : W := mkw 0x0d32800000000000 0x00d3280000000000 0x0e22c00000000000 0x80e22c0000000000

def z545 : W := mkw 0x2612693530bb9ab1 0x42612693530bb9ab 0xee23ce3f71ff1fff 0xbee23ce3f71ff1ff

def z546 : W := mkw 0x4dbbc00069b20008 0x04dbbc00069b2000 0x0fffc00071b80003 0xf0fffc00071b8000

def z547 : W := mkw 0xaf36ab72b068b863 0x0af36ab72b068b86 0xbe3efbf3f078f87e 0xfbe3efbf3f078f87

def z548 : W := mkw 0x8dfb968a00000000 0x08dfb968a0000000 0x0fffc60f00000003 0xe0fffc60f0000000

def z549 : W := mkw 0x1be93e8c5f05d714 0x81be93e8c5f05d71 0x6fe13e0cff87ff8d 0xf6fe13e0cff87ff8

def z550 : W := mkw 0x24160050b068b863 0x024160050b068b86 0x2e1e0000f078f87a 0xf2e1e0000f078f87

def z551 : W := mkw 0x0089000004040000 0x0008900000404000 0x41c100000e070001 0x041c100000e07000

def z552 : W := mkw 0x0000000400010210 0x0000000040001021 0xe0210e0c01c71fff 0xbe0210e0c01c71ff

def z553 : W := mkw 0x40044000edf60008 0x040044000edf6000 0x4023c000ffff000b 0xb4023c000ffff000

def z554 : W := mkw 0x4ffffe00edf60008 0x04ffffe00edf6000 0x4ffffe00ffff000f 0xf4ffffe00ffff000

def z555 : W := mkw 0x0200280010009000 0x0020028001000900 0x6e203e00f180ff8d 0xf6e203e00f180ff8

def z556 : W := mkw 0x849bc1bf009b0ab0 0x4849bc1bf009b0ab 0xf03fcfff01ff1fff 0xbf03fcfff01ff1ff

def z557 : W := mkw 0x4dbf8000ed640008 0x04dbf8000ed64000 0x4ffc0000ff800009 0xf4ffc0000ff80000

def z558 : W := mkw 0x9fffffff86df6ef6 0xc9fffffff86df6ef 0xffffffff8fffffff 0xfffffffff8ffffff

def z559 : W := mkw 0xaf32ab3230289821 0x0af32ab323028982 0x0e22ca3370381800 0x90e22ca337038180

def z560 : W := mkw 0x1dff94cc86456656 0x81dff94cc8645665 0xfffff5cc8e47e67f 0xefffff5cc8e47e67

def z561 : W := mkw 0x220029751009baf3 0x4220029751009baf 0xb0003fff0000fff4 0x0b0003fff0000fff

def z562 : W := mkw 0x0b607e15009b0ab0 0x40b607e15009b0ab 0xefe3fe3f01ff1fff 0xfefe3fe3f01ff1ff

def z563 : W := mkw 0x22042850b068b863 0x022042850b068b86 0x2e003800f078f87c 0xf2e003800f078f87

def z564 : W := mkw 0x40044015edff0ab8 0x440044015edff0ab 0xe023ce3fffff1fff 0xbe023ce3fffff1ff

def z565 : W := mkw 0x10c9148c06054614 0x810c9148c0605461 0xe1c1040c0e47067f 0x2e1c1040c0e47067

def z566 : W := mkw 0x04160010a0680820 0x004160010a068082 0xae1e0830f078187e 0xfae1e0830f078187

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020060001800781 0x0402006000180078

def z568 : W := mkw 0x0d360000e9600000 0x00d360000e960000 0x4ffe0000fff8000b 0xf4ffe0000fff8000

def z569 : W := mkw 0x00cd140086444404 0x000cd14008644440 0x61dd34008e47e60f 0x661dd34008e47e60

def z570 : W := mkw 0x104014cc02016656 0x8104014cc0201665 0xf00135cc0047e67f 0x2f00135cc0047e67

def z571 : W := mkw 0x4fbfe800fdf69008 0x04fbfe800fdf6900 0x6ffff800fffff80f 0xf6ffff800fffff80

def z572 : W := mkw 0x0f723f2000000000 0x00f723f200000000 0x9ffe3ff000000007 0xe9ffe3ff00000000

def z573 : W := mkw 0x2612293030289821 0x0261229303028982 0xae0208307078187e 0xbae0208307078187

def z574 : W := mkw 0x09204015499b0ab0 0x409204015499b0ab 0xefe3ce3fffff1fff 0xfefe3ce3fffff1ff

def z575 : W := mkw 0x0200280010009000 0x0020028001000900 0x200038000000f804 0x0200038000000f80

def z576 : W := mkw 0x24160170a0682863 0x024160170a068286 0x9e1e01f0f078007a 0xf9e1e01f0f078007

def z577 : W := mkw 0x50044044eff7665e 0x850044044eff7665 0x60000000ffffe678 0x160000000ffffe67

def z578 : W := mkw 0x0f763e00fb60d504 0x00f763e00fb60d50 0x6ffe3e00fff8ff8f 0xf6ffe3e00fff8ff8

def z579 : W := mkw 0x9ffbbfae06054614 0x89ffbbfae0605461 0xdfffffff0e070607 0xedfffffff0e07060

def z580 : W := mkw 0x1004004486456656 0x8100400448645665 0xf01c31c08e47e67e 0x6f01c31c08e47e67

def z581 : W := mkw 0x26162960b060b043 0x026162960b060b04 0x1e1e31c0f078e00a 0xf1e1e31c0f078e00

def z582 : W := mkw 0x0040140002004404 0x0004014000200440 0x200034000000e604 0x0200034000000e60

def z583 : W := mkw 0x6dbfc050fdfeb86b 0x06dbfc050fdfeb86 0x6fffc000fffff87b 0xf6fffc000fffff87

def z584 : W := mkw 0x096016005b00d504 0x0096016005b00d50 0x61e00600ff80ff89 0x161e00600ff80ff8

def z585 : W := mkw 0x1bed3ec8df44f546 0x81bed3ec8df44f54 0x7ffc3fc0ff80ff8d 0xf7ffc3fc0ff80ff8

def z586 : W := mkw 0x0000001000080820 0x0000000100008082 0xa000083000001874 0x0a00008300000187

def z587 : W := mkw 0x0612292000000000 0x0061229200000000 0x1e1c31c000000000 0x41e1c31c00000000

def z588 : W := mkw 0x1000000406054614 0x8100000040605461 0x400000000e070600 0x0400000000e07060

def z589 : W := mkw 0x2f763f70fb68fd67 0x02f763f70fb68fd6 0xbfde39f0fe78f87e 0xfbfde39f0fe78f87

def z590 : W := mkw 0x0dbbc015009b0ab0 0x40dbbc015009b0ab 0xefffce3f01ff1fff 0xfefffce3f01ff1ff

def z591 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x8fffce3f00000007 0xe8fffce3f0000000

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c000008e000009 0x641c000008e00000

def z593 : W := mkw 0x4dbfc000a4f60008 0x04dbfc000a4f6000 0x0fffc000007f0003 0xe0fffc000007f000

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000e3f00000004 0x080000e3f0000000

def z595 : W := mkw 0x8fbbabaa00000000 0x08fbbabaa0000000 0x9e3fcbff00000002 0x89e3fcbff0000000

def z596 : W := mkw 0x449fc000a4f60008 0x0449fc000a4f6000 0x0e1fc000f07f000a 0xf0e1fc000f07f000

def z597 : W := mkw 0x24164175a0fb2af3 0x424164175a0fb2af 0xf03fcfff01ff1fff 0xbf03fcfff01ff1ff

def z598 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0x1fdc31c0fe00e000 0x41fdc31c0fe00e00

def z599 : W := mkw 0x20044055b0fbbaf3 0x420044055b0fbbaf 0xe023ce3ff1ffffff 0xbe023ce3ff1fffff

def z600 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xa003c83f007f187e 0xba003c83f007f187

def z601 : W := mkw 0x9fffbfee84452252 0x89fffbfee8445225 0x9fffffff00470077 0xe9fffffff0047007

def z602 : W := mkw 0x0000400500930290 0x4000040050093029 0x0001c00f00070000 0x00001c00f0007000

def z603 : W := mkw 0x100000cc00012252 0x8100000cc0001225 0x900001cc00000070 0x0900001cc0000007

def z604 : W := mkw 0x26162960b060b043 0x026162960b060b04 0xbe1c31c0f040e07e 0x6be1c31c0f040e07

def z605 : W := mkw 0x10cd14dd864d6ef6 0xc10cd14dd864d6ef 0xf1dd3fff8e47ffff 0x6f1dd3fff8e47fff

def z606 : W := mkw 0x8f32ab2200000000 0x08f32ab220000000 0x0e00000000000000 0x00e0000000000000

def z607 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4ffdc000ff870001 0x44ffdc000ff87000

def z608 : W := mkw 0x6fffff70fffefd6f 0x06fffff70fffefd6 0xfffffff0ffffffff 0xffffffff0fffffff

def z609 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x0fe03e00fe00e005 0xe0fe03e00fe00e00

def z610 : W := mkw 0x8f32ab2200000000 0x08f32ab220000000 0x9e3efbf300000006 0xe9e3efbf30000000

def z611 : W := mkw 0x89e9968a00000000 0x089e9968a0000000 0x91fdf7cf00000007 0x691fdf7cf0000000

def z612 : W := mkw 0x5dbfc0ccedf7225a 0x85dbfc0ccedf7225 0xdfffc1ccffff007b 0xfdfffc1ccffff007

def z613 : W := mkw 0x0044144082406446 0x0004414408240644 0xf1dc35c08e40e67f 0x6f1dc35c08e40e67

def z614 : W := mkw 0x0412000020200000 0x0041200002020000 0x0e02000070380000 0x90e0200007038000

def z615 : W := mkw 0x449fc000a4f60008 0x0449fc000a4f6000 0x403fc00001ff000b 0xb403fc00001ff000

def z616 : W := mkw 0x0b20280059009000 0x00b2028005900900 0x6fe03800ff80f80d 0xf6fe03800ff80f80

def z617 : W := mkw 0x104014dd02096ef6 0xc104014dd02096ef 0xb0003fff0000fff4 0x0b0003fff0000fff

def z618 : W := mkw 0x0b607e155b9bdfb4 0x40b607e155b9bdfb 0x6fe03e00fffffffd 0xf6fe03e00fffffff

def z619 : W := mkw 0x10cd14c886446446 0x810cd14c88644644 0xb1dc31c08e40e07e 0x6b1dc31c08e40e07

def z620 : W := mkw 0x4412c00020b20008 0x04412c00020b2000 0x0002c00000380000 0x00002c0000038000

def z621 : W := mkw 0x2612293030289821 0x0261229303028982 0x2e023830f038f80c 0xf2e023830f038f80

def z622 : W := mkw 0x06162800b0609000 0x006162800b060900 0x2e1e3800f078f80e 0xf2e1e3800f078f80

def z623 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x6022ca3301ff1ff8 0x96022ca3301ff1ff

def z624 : W := mkw 0x2000001030289821 0x0200000103028982 0x0000000070381800 0x1000000007038180

def z625 : W := mkw 0x220429709048b863 0x0220429709048b86 0xb01c39f08040f87e 0x6b01c39f08040f87

def z626 : W := mkw 0x8040168a00000000 0x08040168a0000000 0x0000060f00000000 0x00000060f0000000

def z627 : W := mkw 0x0000001500090ab0 0x40000001500090ab 0xa023ce3f00001ff7 0xaa023ce3f00001ff

def z628 : W := mkw 0x000040155b9bdfb4 0x4000040155b9bdfb 0x60000000fffffff8 0x160000000fffffff

def z629 : W := mkw 0x10cd54cd86d766d6 0xc10cd54cd86d766d 0xf1fdf7cf8fc7e7ff 0x6f1fdf7cf8fc7e7f

def z630 : W := mkw 0xcfffffbfedff0ab8 0x4cfffffbfedff0ab 0xffffffffffff1fff 0xfffffffffffff1ff

def z631 : W := mkw 0x2f362b70f968b963 0x02f362b70f968b96 0xbe3e3bf0f1f8f9fe 0xfbe3e3bf0f1f8f9f

def z632 : W := mkw 0x0000400500930290 0x4000040050093029 0x6021ce0f01871f8d 0xb6021ce0f01871f8

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000001801f88 0x16000000001801f8

def z634 : W := mkw 0x24160170a0682863 0x024160170a068286 0xb01e09f00078187e 0xbb01e09f00078187

def z635 : W := mkw 0x10cd14dc864d6e76 0x810cd14dc864d6e7 0xf1df3dfc8e7ffe7f 0xff1df3dfc8e7ffe7

def z636 : W := mkw 0xafffffffb0fbbaf3 0x4afffffffb0fbbaf 0xfffffffff1ffffff 0xffffffffff1fffff

def z637 : W := mkw 0x0bed3e00df44d504 0x00bed3e00df44d50 0x6ffd3e00ffc7ff8f 0xf6ffd3e00ffc7ff8

def z638 : W := mkw 0x096014004b004404 0x0096014004b00440 0x6fe03400ff80e60d 0xf6fe03400ff80e60

def z639 : W := mkw 0x10c9148c06054614 0x810c9148c0605461 0xd1dd35cc0e070607 0x6d1dd35cc0e07060

def z640 : W := mkw 0xaffbbfba30289821 0x0affbbfba3028982 0x9fffffff70381807 0xf9fffffff7038180

def z641 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0x6022ce3301b81f8d 0xb6022ce3301b81f8

def z642 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xb01e39f00078f876 0x0b01e39f00078f87

def z643 : W := mkw 0x00004010009a0820 0x000004010009a082 0xe023c83001ff187f 0xbe023c83001ff187

def z644 : W := mkw 0x0000400000920000 0x0000040000092000 0x0022c00001b80000 0x90022c00001b8000

def z645 : W := mkw 0x49a9c0154d9f0ab8 0x449a9c0154d9f0ab 0xe1e3ce3f0fff1fff 0xbe1e3ce3f0fff1ff

def z646 : W := mkw 0x89e9d69f009b0ab0 0x489e9d69f009b0ab 0xe1e3ce3f01ff1fff 0xbe1e3ce3f01ff1ff

def z647 : W := mkw 0x449f8000a4640008 0x0449f8000a464000 0x001c000000000000 0x0001c00000000000

def z648 : W := mkw 0x19e9168c4f054714 0x819e9168c4f05471 0x41e1060c0f870781 0x041e1060c0f87078

def z649 : W := mkw 0x26162970fb68fd67 0x026162970fb68fd6 0xfe1e39f0fff8fffe 0xffe1e39f0fff8fff

def z650 : W := mkw 0x22006975109bbaf3 0x422006975109bbaf 0xf023ffff01ffffff 0xbf023ffff01fffff

def z651 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0e3fc00071ff0002 0x90e3fc00071ff000

def z652 : W := mkw 0x12403ecc1201f756 0x812403ecc1201f75 0xb0003fcc0000fff4 0x0b0003fcc0000fff

def z653 : W := mkw 0x869ba9aa00000000 0x0869ba9aa0000000 0x9e1ff9ff00000006 0xe9e1ff9ff0000000

def z654 : W := mkw 0x0b202a0059009100 0x00b202a005900910 0x2e203a00f180f98c 0xf2e203a00f180f98

def z655 : W := mkw 0x549fc0cca4f7225a 0x8549fc0cca4f7225 0x901fc1cc007f0072 0x0901fc1cc007f007

def z656 : W := mkw 0x00405415029b4eb4 0x400405415029b4eb 0xe1e3fe3f8fffffff 0xfe1e3fe3f8ffffff

def z657 : W := mkw 0x02403e0000000000 0x002403e000000000 0x00003e0000000004 0x000003e000000000

def z658 : W := mkw 0x0000000400010210 0x0000000040001021 0x6000000000470678 0x0600000000047067

def z659 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe0000e3f01ff1ffc 0x1e0000e3f01ff1ff

def z660 : W := mkw 0x0000400000920000 0x0000040000092000 0xc023ce3f01ff000f 0xbc023ce3f01ff000

def z661 : W := mkw 0x108d40dd84df2af2 0xc108d40dd84df2af 0x901fc1ff007f0072 0x0901fc1ff007f007

def z662 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0x0000000001b81980 0x10000000001b8198

def z663 : W := mkw 0x6fbfe960fdf6b04b 0x06fbfe960fdf6b04 0x5ffff1c0ffffe00b 0xf5ffff1c0ffffe00

def z664 : W := mkw 0x4fffbe00ff64d50c 0x04fffbe00ff64d50 0x6ffc3e00ff80ff8d 0xf6ffc3e00ff80ff8

def z665 : W := mkw 0x2f322b3079289921 0x02f322b307928992 0x0e220a3071b81980 0x90e220a3071b8198

def z666 : W := mkw 0x26162974b069ba73 0x026162974b069ba7 0xfe1f3dfcf07ffe7f 0xffe1f3dfcf07ffe7

def z667 : W := mkw 0x0000400000920000 0x0000040000092000 0x0003c000007f0002 0x00003c000007f000

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x000200000078000a 0xb000200000078000

def z669 : W := mkw 0x0200292000000000 0x0020029200000000 0x900039f000000004 0x0900039f00000000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x600004000000060d 0x2600004000000060

def z671 : W := mkw 0x5dff94ccef65665e 0x85dff94ccef65665 0xffdd35ccfe47e67f 0x6ffdd35ccfe47e67

def z672 : W := mkw 0x49e9d6004f96450c 0x049e9d6004f96450 0x41e1c6000f870781 0x041e1c6000f87078

def z673 : W := mkw 0x349f01fca46d2a73 0x8349f01fca46d2a7 0x901f01fc007f0072 0x0901f01fc007f007

def z674 : W := mkw 0x4fffbe00ff64d50c 0x04fffbe00ff64d50 0x0fdc3000fe00e000 0x40fdc3000fe00e00

def z675 : W := mkw 0x54dfd4cca6f7665e 0x854dfd4cca6f7665 0xf1dff5cc8e7fe67f 0x6f1dff5cc8e7fe67

def z676 : W := mkw 0x8f32ab2200000000 0x08f32ab220000000 0x8e23ce3f00000007 0xa8e23ce3f0000000

def z677 : W := mkw 0x26162960b060b043 0x026162960b060b04 0x3e1c39c0f000f80c 0xf3e1c39c0f000f80

def z678 : W := mkw 0x4d32c00069b20008 0x04d32c00069b2000 0x4fe2c000ffb80009 0xf4fe2c000ffb8000

def z679 : W := mkw 0x8be9be8a00000000 0x08be9be8a0000000 0x0fe1fe0f00000005 0xe0fe1fe0f0000000

def z680 : W := mkw 0x60044050fdfeb86b 0x060044050fdfeb86 0x60000000fffff878 0x160000000fffff87

def z681 : W := mkw 0x220029701008b863 0x0220029701008b86 0xb00239f00078f87e 0xbb00239f00078f87

def z682 : W := mkw 0x0f723f205b00d504 0x00f723f205b00d50 0xfffe3ff0ff80ff8f 0xffffe3ff0ff80ff8

def z683 : W := mkw 0xcdffd68aedf60008 0x0cdffd68aedf6000 0x4fffc60fffff000b 0xf4fffc60fffff000

def z684 : W := mkw 0x89e9968a00000000 0x089e9968a0000000 0x81e3ce3f00000007 0xa81e3ce3f0000000

def z685 : W := mkw 0x0920000049000000 0x0092000004900000 0x6fe00e00ff801f8d 0xf6fe00e00ff801f8

def z686 : W := mkw 0x8f72bf2200000000 0x08f72bf220000000 0x0fe2fe3300000005 0xe0fe2fe330000000

def z687 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xd1dd05cc0e470673 0x0d1dd05cc0e47067

def z688 : W := mkw 0x0040148800000000 0x0004014880000000 0x900035cc00000004 0x0900035cc0000000

def z689 : W := mkw 0x26166975b0fbbaf3 0x426166975b0fbbaf 0xbe1ff9fff07ff87e 0xfbe1ff9fff07ff87

def z690 : W := mkw 0xcfffffaaa4f60008 0x0cfffffaaa4f6000 0x9fffffff007f0007 0xe9fffffff007f000

def z691 : W := mkw 0x02403e001200d504 0x002403e001200d50 0x2e003e00f000ff8c 0xf2e003e00f000ff8

def z692 : W := mkw 0x4dbfc004edf70218 0x04dbfc004edf7021 0xefffc40cffff067f 0xfefffc40cffff067

def z693 : W := mkw 0x1bed7edddfdffff6 0xc1bed7edddfdffff 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x2fc03e00fe00ff84 0x42fc03e00fe00ff8

def z695 : W := mkw 0x10cd14c886446446 0x810cd14c88644644 0x51dd31c08e47e00b 0x651dd31c08e47e00

def z696 : W := mkw 0x02403e001200d504 0x002403e001200d50 0x61c03e008e00ff8d 0x661c03e008e00ff8

def z697 : W := mkw 0x36df3df8b66cfc67 0x836df3df8b66cfc6 0xbfde39f0fe78f87e 0xfbfde39f0fe78f87

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e000000f0000008 0xf0e000000f000000

def z699 : W := mkw 0x5dffd48ceff7461c 0x85dffd48ceff7461 0x4fffc40cffff060b 0xf4fffc40cffff060

def z700 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x0fe03a00ff80f980 0xd0fe03a00ff80f98

def z701 : W := mkw 0x669fe970b4feb86b 0x0669fe970b4feb86 0xbe1ff9f0f07ff87e 0xfbe1ff9f0f07ff87

def z702 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x0fe3ce3f00000001 0x80fe3ce3f0000000

def z703 : W := mkw 0x4dffd488edf60008 0x04dffd488edf6000 0xdffff5ccffff000f 0xfdffff5ccffff000

def z704 : W := mkw 0x0000001000080820 0x0000000100008082 0xa023ce3f0078187f 0xba023ce3f0078187

def z705 : W := mkw 0x00004011009a08a0 0x400004011009a08a 0xa022ca3301f819fe 0xba022ca3301f819f

def z706 : W := mkw 0x0b603e0059009100 0x00b603e005900910 0x0fe03e0071801985 0xf0fe03e007180198

def z707 : W := mkw 0x0dbbc00049920000 0x00dbbc0004992000 0x4fffc000ffff000b 0xf4fffc000ffff000

def z708 : W := mkw 0x849b81aa5b00d504 0x0849b81aa5b00d50 0xf01fc1ffff80ff8a 0x1f01fc1ffff80ff8

def z709 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x91dfc1ff00000003 0x691dfc1ff0000000

def z710 : W := mkw 0x09ad4000cdd60000 0x009ad4000cdd6000 0x4fffc000ffff000b 0xf4fffc000ffff000

def z711 : W := mkw 0x8f32eb33599a99a0 0x48f32eb33599a99a 0x0e22ca3371b81980 0x90e22ca3371b8198

def z712 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffc0007fff0003 0x94fffc0007fff000

def z713 : W := mkw 0x24160050b068b863 0x024160050b068b86 0xbe1e31c0f078f87e 0xfbe1e31c0f078f87

def z714 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0x9fdff1fffe00e002 0x49fdff1fffe00e00

def z715 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9ffeffff00000004 0xc9ffeffff0000000

def z716 : W := mkw 0x4dbf8015ed6d0ab8 0x44dbf8015ed6d0ab 0xafdc0e3ffe001ff4 0x4afdc0e3ffe001ff

def z717 : W := mkw 0x4dbbc0006db60008 0x04dbbc0006db6000 0x4fe3c000ffbf0009 0xf4fe3c000ffbf000

def z718 : W := mkw 0x5d72d4cc6bb3665e 0x85d72d4cc6bb3665 0xbe22f5cc71b8e674 0x9be22f5cc71b8e67

def z719 : W := mkw 0x02403c001200d404 0x002403c001200d40 0x6fe03e00ff80ff8d 0xf6fe03e00ff80ff8

def z720 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x9fdfc1ff00000002 0x49fdfc1ff0000000

def z721 : W := mkw 0x8dfb97aa4b004504 0x08dfb97aa4b00450 0xd1ffc7ff0f800783 0x0d1ffc7ff0f80078

def z722 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe03000ff80ff89 0xf6fe03000ff80ff8

def z723 : W := mkw 0x36db3dbc362dde35 0x836db3dbc362dde3 0x4fc30c3c7e3f1e01 0x94fc30c3c7e3f1e0

def z724 : W := mkw 0x8ffbbfaa1200d504 0x08ffbbfaa1200d50 0xffffffff8e00ff8f 0xeffffffff8e00ff8

def z725 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd3fcc8e47ffff 0x6f1dd3fcc8e47fff

def z726 : W := mkw 0x0f723f2000000000 0x00f723f200000000 0x9fffffff00000007 0xe9fffffff0000000

def z727 : W := mkw 0x8ffbbfaa49000100 0x08ffbbfaa4900010 0x9fffffff01800187 0xe9fffffff0180018

def z728 : W := mkw 0x10cd16cc86456756 0x810cd16cc8645675 0xf1dd37cc8e47e7ff 0x6f1dd37cc8e47e7f

def z729 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xfe3ffffff1f8ffff 0xffe3ffffff1f8fff

def z730 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0fffc000fe7f0003 0xe0fffc000fe7f000

def z731 : W := mkw 0x49244000edf60008 0x049244000edf6000 0x4fe3c000ffff000b 0xf4fe3c000ffff000

def z732 : W := mkw 0x10cd54d986de6ce6 0xc10cd54d986de6ce 0x11fefbf38fb8f980 0xd11fefbf38fb8f98

def z733 : W := mkw 0x6ba9e9705d9eb86b 0x06ba9e9705d9eb86 0xf1e1f9f00f87f875 0x0f1e1f9f00f87f87

def z734 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fc03800ff80ff8c 0xf6fc03800ff80ff8

def z735 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd3fff8e47e67f 0x6f1dd3fff8e47e67

def z736 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe00e00ff80ff89 0x96fe00e00ff80ff8

def z737 : W := mkw 0x26162b70b068b963 0x026162b70b068b96 0xbe1e3bf0f078f9fe 0xfbe1e3bf0f078f9f

def z738 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9ffff1ff00000003 0xe9ffff1ff0000000

def z739 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffca33ffff000b 0xf4fffca33ffff000

def z740 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe03e00ff80ff85 0x46fe03e00ff80ff8

def z741 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1fdf7cf8e47e67f 0x6f1fdf7cf8e47e67

def z742 : W := mkw 0x092000005b00d504 0x0092000005b00d50 0x6fc00000ff80ff88 0x56fc00000ff80ff8

def z743 : W := mkw 0xa616a972b068b863 0x0a616a972b068b86 0xbe1ef9f3f078f87e 0xfbe1ef9f3f078f87

def z744 : W := mkw 0x49adc000edf60008 0x049adc000edf6000 0x4fe1c000ffff0009 0xf4fe1c000ffff000

def z745 : W := mkw 0x59e9d48d4f97469c 0xc59e9d48d4f97469 0x41e1c60f0f870781 0x041e1c60f0f87078

def z746 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x11dc31c08e47e070 0x411dc31c08e47e07

def z747 : W := mkw 0x26166965b0f3b2d3 0x426166965b0f3b2d 0x5e3df7cff187e781 0x45e3df7cff187e78

def z748 : W := mkw 0xc2447faaedf60008 0x0c2447faaedf6000 0xd0003fffffff000c 0x1d0003fffffff000

def z749 : W := mkw 0x8ffbbfaa02004404 0x08ffbbfaa0200440 0x9fffffff8e00e007 0xe9fffffff8e00e00

def z750 : W := mkw 0x8ffbbfaa4b004504 0x08ffbbfaa4b00450 0xffffffff8f80e78f 0xeffffffff8f80e78

def z751 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fdff9ff00000006 0xe9fdff9ff0000000

def z752 : W := mkw 0x46dffe00b6f6d50c 0x046dffe00b6f6d50 0x201ffe00007fff86 0x0201ffe00007fff8

def z753 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1df3dfc8e47e67f 0xef1df3dfc8e47e67

def z754 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xbffffffffe00f80f 0xfbffffffffe00f80

def z755 : W := mkw 0x0b202a005b00d504 0x00b202a005b00d50 0x6fe00a00ff80ff89 0xf6fe00a00ff80ff8

def z756 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fffffff0078000f 0xf9fffffff0078000

def z757 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe1e3ce3f8fff1fff 0xfe1e3ce3f8fff1ff

def z758 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xee23ce3ff1ff1fff 0xfee23ce3ff1ff1ff

def z759 : W := mkw 0x22042850b068b863 0x022042850b068b86 0xbe1c39c0f078f87e 0xfbe1c39c0f078f87

def z760 : W := mkw 0xa9ed96dab068b863 0x0a9ed96dab068b86 0x21e1c60ff078f879 0x121e1c60ff078f87

def z761 : W := mkw 0x5dbfc0c8edf6204a 0x85dbfc0c8edf6204 0x5fffc1c0ffff000b 0xf5fffc1c0ffff000

def z762 : W := mkw 0x22403f751209fff7 0x422403f751209fff 0xb0003fff0000fff4 0x0b0003fff0000fff

def z763 : W := mkw 0x8ffbffbf009b0ab0 0x48ffbffbf009b0ab 0x7fdc31c001ff1ff8 0x57fdc31c001ff1ff

def z764 : W := mkw 0x8ffbbfaa02004404 0x08ffbbfaa0200440 0xdfffffff0e000607 0xedfffffff0e00060

def z765 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x3e1c39c0f078f87c 0xf3e1c39c0f078f87

def z766 : W := mkw 0x4dbfc200edf60108 0x04dbfc200edf6010 0x4fffc200ffff018b 0xf4fffc200ffff018

def z767 : W := mkw 0x8b60be025b00d504 0x08b60be025b00d50 0x6fe0fe03ff80ff8d 0xf6fe0fe03ff80ff8

def z768 : W := mkw 0x0b607e155b9bdfb4 0x40b607e155b9bdfb 0x8fc3f03ffe7fe072 0x48fc3f03ffe7fe07

def z769 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xdfffffffff80e787 0xedfffffffff80e78

def z770 : W := mkw 0xa6162b72b068b863 0x0a6162b72b068b86 0xbe1e3bf3f078f87e 0xfbe1e3bf3f078f87

def z771 : W := mkw 0x1004405586df6ef6 0xc1004405586df6ef 0x600000008e7fe678 0x0600000008e7fe67

def z772 : W := mkw 0x0f723f205b00d504 0x00f723f205b00d50 0xffffffffff80ff8f 0xfffffffffff80ff8

def z773 : W := mkw 0x1bad2accdd45b352 0x81bad2accdd45b35 0x9e3d0bcc71c719f2 0x99e3d0bcc71c719f

def z774 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e3ff0f078fffe 0xfbe1e3ff0f078fff

def z775 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe3efbf3f078f87e 0xfbe3efbf3f078f87

def z776 : W := mkw 0x59e9d68c4f97471c 0x859e9d68c4f97471 0x41e1c60c0f870781 0x041e1c60c0f87078

def z777 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xcfffc40cffff000f 0xfcfffc40cffff000

def z778 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xbfffffff0000180f 0xfbfffffff0000180

def z779 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fdfc000ffff000a 0x54fdfc000ffff000

def z780 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fe3c000ffff0009 0x94fe3c000ffff000

def z781 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901fc5ff00000007 0x2901fc5ff0000000

def z782 : W := mkw 0x096016005b00d504 0x0096016005b00d50 0x6fe00600ff80ff89 0xf6fe00600ff80ff8

def z783 : W := mkw 0x869ba9aa10009000 0x0869ba9aa1000900 0xbe1ff9fff000f80e 0xfbe1ff9fff000f80

def z784 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x91dd35cc8e47e077 0x691dd35cc8e47e07

def z785 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd35cc8fc7ffff 0x7f1dd35cc8fc7fff

def z786 : W := mkw 0x89e9d68f4b934794 0x489e9d68f4b93479 0x41e1c60f0f870781 0x041e1c60f0f87078

def z787 : W := mkw 0x26162960b060b043 0x026162960b060b04 0xbe1e31c0f078e07e 0xfbe1e31c0f078e07

def z788 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0xf03fcfff01801f8f 0xbf03fcfff01801f8

def z789 : W := mkw 0x0be93e885b00d504 0x00be93e885b00d50 0xffffffffff80ff8f 0xfffffffffff80ff8

def z790 : W := mkw 0x8ffbbfaa59009100 0x08ffbbfaa5900910 0xffffffff71801f8f 0xfffffffff71801f8

def z791 : W := mkw 0x8dfb97aa00000000 0x08dfb97aa0000000 0x91fff7ff00000007 0x691fff7ff0000000

def z792 : W := mkw 0x06db3da800000000 0x006db3da80000000 0x9fffffff00000007 0xe9fffffff0000000

def z793 : W := mkw 0x06162960a0602042 0x006162960a060204 0xbe1e39f0f078e07e 0xfbe1e39f0f078e07

def z794 : W := mkw 0x8ffbbfaa1200d504 0x08ffbbfaa1200d50 0xbffffffff000ff8f 0xfbffffffff000ff8

def z795 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe1fe0fff80ff8d 0xf6fe1fe0fff80ff8

def z796 : W := mkw 0x8fbbabaa00000000 0x08fbbabaa0000000 0x9fffcbff00000003 0xe9fffcbff0000000

def z797 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd31cc8e47e67a 0x4f1dd31cc8e47e67

def z798 : W := mkw 0x8ffbbfaa10009000 0x08ffbbfaa1000900 0x9ffffffff000e007 0xe9ffffffff000e00

def z799 : W := mkw 0x9f36ab6686456656 0x89f36ab668645665 0x6e22ca338e47e678 0x86e22ca338e47e67

def z800 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1c31c0f078f87e 0x7be1c31c0f078f87

def z801 : W := mkw 0x86dbbfaa00000000 0x086dbbfaa0000000 0x91dfffff00000007 0x691dfffff0000000

def z802 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1ff9fff078f87e 0xfbe1ff9fff078f87

def z803 : W := mkw 0x84db95aa00000000 0x084db95aa0000000 0x91ffffff00000007 0xe91ffffff0000000

def z804 : W := mkw 0x8dfb97aa00000000 0x08dfb97aa0000000 0x91dfc1ff00000002 0x091dfc1ff0000000

def z805 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x9e1fc1ff00000002 0xe9e1fc1ff0000000

def z806 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1c39f0f078f87c 0x5be1c39f0f078f87

def z807 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x9e1e39f0f078e076 0xe9e1e39f0f078e07

def z808 : W := mkw 0x8ffbbfaa1200d404 0x08ffbbfaa1200d40 0xfffffffffe00fe0f 0xffffffffffe00fe0

def z809 : W := mkw 0x8ffbbfaa49000000 0x08ffbbfaa4900000 0x9fffffff71800007 0xf9fffffff7180000

def z810 : W := mkw 0x4d364000edf60008 0x04d364000edf6000 0x4ffe0000ffff000b 0xf4ffe0000ffff000

def z811 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901ff1ff00000006 0x6901ff1ff0000000

def z812 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x6fffc400ffff060f 0xf6fffc400ffff060

def z813 : W := mkw 0xcdbfc08aedf60008 0x0cdbfc08aedf6000 0x4fffc00fffff000b 0xf4fffc00fffff000

def z814 : W := mkw 0x0000000000000000 0x0000000000000000 0x903fffff00000007 0xe903fffff0000000

def z815 : W := mkw 0x8ffbbfaa10009100 0x08ffbbfaa1000910 0x9fffffff00001987 0xe9fffffff0000198

def z816 : W := mkw 0x90cd94ce86456656 0x890cd94ce8645665 0xf1ddf5cf8e47e67f 0x6f1ddf5cf8e47e67

def z817 : W := mkw 0x10c914cc06056656 0x810c914cc0605665 0xf1dd35cc0e07e677 0x6f1dd35cc0e07e67

def z818 : W := mkw 0x20044055b0fbbaf3 0x420044055b0fbbaf 0x20000000f07ff878 0x120000000f07ff87

def z819 : W := mkw 0x0412012000000000 0x0041201200000000 0x903fcfff00000007 0xa903fcfff0000000

def z820 : W := mkw 0x9ffbbfaa06044404 0x89ffbbfaa0604440 0x9fffffff0e000007 0xe9fffffff0e00000

def z821 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dc35cc8e47e67c 0x4f1dc35cc8e47e67

def z822 : W := mkw 0x2d761770eb686d67 0x02d761770eb686d6 0xd1fe07f00ff807f3 0x0d1fe07f00ff807f

def z823 : W := mkw 0x6f32e93179ba98a9 0x46f32e93179ba98a 0x0e22ca3371b81980 0x90e22ca3371b8198

def z824 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xfe1e39f0f1f8fffe 0xffe1e39f0f1f8fff

def z825 : W := mkw 0x4dbfc088edf60008 0x04dbfc088edf6000 0xdfffc1ccffff000b 0xfdfffc1ccffff000

def z826 : W := mkw 0x82403fbf1209dfb4 0x482403fbf1209dfb 0xb0003fff0000fff4 0x0b0003fff0000fff

def z827 : W := mkw 0x1044144486456656 0x8104414448645665 0xf1dc35c08e47e67f 0x6f1dc35c08e47e67

def z828 : W := mkw 0x8dbb83aa00000000 0x08dbb83aa0000000 0x903fc3ff00000002 0x0903fc3ff0000000

def z829 : W := mkw 0x8ffbbfaa4b004404 0x08ffbbfaa4b00440 0xffffffffff80e60f 0xfffffffffff80e60

def z830 : W := mkw 0x00cd144086446446 0x000cd14408644644 0xf1dd35c08e47e67f 0x6f1dd35c08e47e67

def z831 : W := mkw 0x84db97aa00000000 0x084db97aa0000000 0x901fc7ff00000002 0x0901fc7ff0000000

def z832 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xfe1e3df0f078fe7f 0xffe1e3df0f078fe7

def z833 : W := mkw 0x86523faa00000000 0x086523faa0000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z834 : W := mkw 0x0dbf8000a4640000 0x00dbf8000a464000 0x4fffc000fe7f000b 0xf4fffc000fe7f000

def z835 : W := mkw 0x0089008800000000 0x0008900880000000 0x901fc1ff00000002 0x0901fc1ff0000000

def z836 : W := mkw 0xcffbbfaa4d040008 0x0cffbbfaa4d04000 0x9fffffff0e000007 0xe9fffffff0e00000

def z837 : W := mkw 0xcdbfc1aaedf60008 0x0cdbfc1aaedf6000 0x5fffc1c0ffff000b 0xf5fffc1c0ffff000

def z838 : W := mkw 0xcdbfc122edf60008 0x0cdbfc122edf6000 0x4fffc033ffff000b 0xf4fffc033ffff000

def z839 : W := mkw 0x4dbfc040edf6204a 0x04dbfc040edf6204 0x5ffff1c0ffffe00b 0xf5ffff1c0ffffe00

def z840 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x4fe03e00ff80ff81 0xd4fe03e00ff80ff8

def z841 : W := mkw 0x8ffbbfaa1200d504 0x08ffbbfaa1200d50 0xffffffff0180ff8f 0xfffffffff0180ff8

def z842 : W := mkw 0x4d36c000edf60008 0x04d36c000edf6000 0x4fe2c000ffff0009 0xf4fe2c000ffff000

def z843 : W := mkw 0x02403c005b00d504 0x002403c005b00d50 0x6fc03c00ff80ff8d 0xf6fc03c00ff80ff8

def z844 : W := mkw 0x869babaa00000000 0x0869babaa0000000 0x901fcbff00000002 0x0901fcbff0000000

def z845 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903fcbff00000002 0x8903fcbff0000000

def z846 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x1e1c31c0f078e070 0x41e1c31c0f078e07

def z847 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe23e00fff8ff8f 0xf6fe23e00fff8ff8

def z848 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe03600ff80ff89 0x56fe03600ff80ff8

def z849 : W := mkw 0x8ffbbfaa4b004504 0x08ffbbfaa4b00450 0xffffffff0f801f8f 0xfffffffff0f801f8

def z850 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xdfffffff0047000f 0xedfffffff0047000

def z851 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fdd0000ffff000b 0x74fdd0000ffff000

def z852 : W := mkw 0x108d00cc84452252 0x8108d00cc8445225 0xf1dd31cc8e47e07f 0x6f1dd31cc8e47e07

def z853 : W := mkw 0x8fbbabaa00000000 0x08fbbabaa0000000 0x9e3fcfff00000007 0xa9e3fcfff0000000

def z854 : W := mkw 0x0b20280059009000 0x00b2028005900900 0x6fe03e00ff80ff8d 0xf6fe03e00ff80ff8

def z855 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe3fe00ff80ff8f 0xf6fe3fe00ff80ff8

def z856 : W := mkw 0x8ffbbfaa02004404 0x08ffbbfaa0200440 0xbfffffff0000e607 0xebfffffff0000e60

def z857 : W := mkw 0x145614cca2616656 0x8145614cca261665 0xbe1e35ccf078e67e 0xfbe1e35ccf078e67

def z858 : W := mkw 0x49ad4000edf60008 0x049ad4000edf6000 0x4ffd0000ffff000b 0xf4ffd0000ffff000

def z859 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e39f0f078f876 0x4be1e39f0f078f87

def z860 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xefffce3fffff1f8f 0xfefffce3fffff1f8

def z861 : W := mkw 0x008d004484452252 0x0008d00448445225 0xf1dd35cc8e47e67f 0x6f1dd35cc8e47e67

def z862 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fc03e00ff80ff8c 0x56fc03e00ff80ff8

def z863 : W := mkw 0x02407e001292d504 0x002407e001292d50 0x6023fe0001ffff8f 0xb6023fe0001ffff8

def z864 : W := mkw 0x8ffbbfaa49000000 0x08ffbbfaa4900000 0xdfffffff0f800007 0xedfffffff0f80000

def z865 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x71dc35c08e47e67d 0x671dc35c08e47e67

def z866 : W := mkw 0x22046855b0fbbaf3 0x422046855b0fbbaf 0x6e203e00f1fffffd 0xf6e203e00f1fffff

def z867 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1ffffff8fc7ffff 0xff1ffffff8fc7fff

def z868 : W := mkw 0x06162840b060b042 0x006162840b060b04 0xbe1e39c0f078f87e 0xfbe1e39c0f078f87

def z869 : W := mkw 0x0612292010009000 0x0061229201000900 0xfe3ffffff180ff8f 0xffe3ffffff180ff8

def z870 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1fff5cc8e47e67f 0xef1fff5cc8e47e67

def z871 : W := mkw 0x26162971b068b8e3 0x426162971b068b8e 0xbe1e3bf3f078f9fe 0xfbe1e3bf3f078f9f

def z872 : W := mkw 0x349f41fda4ff2af3 0xc349f41fda4ff2af 0x901fc1ff007f0072 0x0901fc1ff007f007

def z873 : W := mkw 0x8b603faa5b00d504 0x08b603faa5b00d50 0x7fe03fc0ff80ff8d 0xf7fe03fc0ff80ff8

def z874 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd35cc0e47e677 0x0f1dd35cc0e47e67

def z875 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e31f0f078e07e 0x6be1e31f0f078e07

def z876 : W := mkw 0x4dbfc120edf60008 0x04dbfc120edf6000 0xdfffc1f0ffff000b 0xfdfffc1f0ffff000

def z877 : W := mkw 0xaffbbfaa30209001 0x0affbbfaa3020900 0x9fffffff70000007 0xe9fffffff7000000

def z878 : W := mkw 0x8fbbabaa00000000 0x08fbbabaa0000000 0x9e1fc1ff00000002 0x09e1fc1ff0000000

def z879 : W := mkw 0x10cd14cd864566d6 0xc10cd14cd864566d 0xf1dd37cf8e47e7ff 0x6f1dd37cf8e47e7f

def z880 : W := mkw 0x8dfb97aa00000000 0x08dfb97aa0000000 0x9fffc7ff00000003 0xe9fffc7ff0000000

def z881 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dff5ff8e47e67f 0x6f1dff5ff8e47e67

def z882 : W := mkw 0x8ffbbfaa59009100 0x08ffbbfaa5900910 0xbffffffff180f98f 0xfbffffffff180f98

def z883 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xdfffffff8e00000f 0xedfffffff8e00000

def z884 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe023fe3f81ffffff 0xfe023fe3f81fffff

def z885 : W := mkw 0x8fbbabaa00000000 0x08fbbabaa0000000 0x9e3ffbff00000006 0xe9e3ffbff0000000

def z886 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xdffff1c0ffff000f 0xfdffff1c0ffff000

def z887 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xdfffffff01800787 0xedfffffff0180078

def z888 : W := mkw 0xcffbbfaa69200008 0x0cffbbfaa6920000 0x9fffffff70000007 0xe9fffffff7000000

def z889 : W := mkw 0x86dbbfaa00000000 0x086dbbfaa0000000 0x9e1fffff00000006 0xe9e1fffff0000000

def z890 : W := mkw 0x1004405584df2af2 0xc1004405584df2af 0x00000000007f0070 0x000000000007f007

def z891 : W := mkw 0x8ffbbfaa10009000 0x08ffbbfaa1000900 0x9fffffff70001807 0xf9fffffff7000180

def z892 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x9e1e39f0f078f872 0xd9e1e39f0f078f87

def z893 : W := mkw 0x1004405584df2af2 0xc1004405584df2af 0x6000000001ff1ff8 0x16000000001ff1ff

def z894 : W := mkw 0x84db95aa00000000 0x084db95aa0000000 0x901ff5ff00000006 0x0901ff5ff0000000

def z895 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffc000ffff0003 0x44fffc000ffff000

def z896 : W := mkw 0x89e9968a00000000 0x089e9968a0000000 0x91ffffff00000007 0xe91ffffff0000000

def z897 : W := mkw 0x096014004b004404 0x0096014004b00440 0x6fe03e00ff80ff8d 0xf6fe03e00ff80ff8

def z898 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1df35cc8e7fe67f 0xff1df35cc8e7fe67

def z899 : W := mkw 0x0044144482416656 0x0004414448241665 0xf1dd35cc8e47e67f 0x6f1dd35cc8e47e67

def z900 : W := mkw 0x869ba9aa00000000 0x0869ba9aa0000000 0x9e1fc9ff00000002 0x89e1fc9ff0000000

def z901 : W := mkw 0x4dbfc040edf6204a 0x04dbfc040edf6204 0xdfffc1c0ffff007b 0xfdfffc1c0ffff007

def z902 : W := mkw 0x86dbbfaa1200d504 0x086dbbfaa1200d50 0xb01fffff0000ff86 0x0b01fffff0000ff8

def z903 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x91ffc1ff00000003 0x091ffc1ff0000000

def z904 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffc60fffff000b 0xf4fffc60fffff000

def z905 : W := mkw 0x00c9148c02014614 0x000c9148c0201461 0xf1dd35cc8e47e67f 0x6f1dd35cc8e47e67

def z906 : W := mkw 0x8ffbbfaa59009000 0x08ffbbfaa5900900 0xffffffffff80f80f 0xfffffffffff80f80

def z907 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe2fe33ff80ff8d 0xf6fe2fe33ff80ff8

def z908 : W := mkw 0x84db95aa00000000 0x084db95aa0000000 0x91dfc5ff00000003 0x091dfc5ff0000000

def z909 : W := mkw 0x30044055b6fffef7 0xc30044055b6fffef 0x60000000fffffff8 0x160000000fffffff

def z910 : W := mkw 0x4dbbc0006db60008 0x04dbbc0006db6000 0x4fe3c0007fff000b 0xb4fe3c0007fff000

def z911 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0fdc0000fe7f0000 0x40fdc0000fe7f000

def z912 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9ffffbff00000002 0xc9ffffbff0000000

def z913 : W := mkw 0x869ba9aa00000000 0x0869ba9aa0000000 0x901ff9ff00000006 0x0901ff9ff0000000

def z914 : W := mkw 0x0b603f205b00d504 0x00b603f205b00d50 0xffe03ff0ff80ff8d 0xfffe03ff0ff80ff8

def z915 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x6ffff000ffffe00f 0xf6ffff000ffffe00

def z916 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fdfc000fe7f000b 0x64fdfc000fe7f000

def z917 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x6fffc800ffff180f 0xf6fffc800ffff180

def z918 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x9e1e31f0f078e07a 0xf9e1e31f0f078e07

def z919 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fde0000ffff000a 0xf4fde0000ffff000

def z920 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xffde39f0fe78f87f 0xfffde39f0fe78f87

def z921 : W := mkw 0x0dbf0000ed640000 0x00dbf0000ed64000 0x4fff0000ffff000b 0xf4fff0000ffff000

def z922 : W := mkw 0x108d004486456656 0x8108d00448645665 0xf1dd31c08e47e67f 0x6f1dd31c08e47e67

def z923 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe3e3bf0f1f8f9fe 0xfbe3e3bf0f1f8f9f

def z924 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xd1dd35cc8e47e673 0x4d1dd35cc8e47e67

def z925 : W := mkw 0x2f326b3179ba99a1 0x42f326b3179ba99a 0x0e22ca3371b81980 0x90e22ca3371b8198

def z926 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xcfffc03fffff000b 0xfcfffc03fffff000

def z927 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe3e3ff0f078f87f 0xfbe3e3ff0f078f87

def z928 : W := mkw 0x449f4000edf60008 0x0449f4000edf6000 0x4fdf0000ffff000b 0xf4fdf0000ffff000

def z929 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903fc7ff00000003 0x0903fc7ff0000000

def z930 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1fd35cc8fc7e67f 0xff1fd35cc8fc7e67

def z931 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0xefe03e00ffc0ffff 0xfefe03e00ffc0fff

def z932 : W := mkw 0x8ffbbfaa10009000 0x08ffbbfaa1000900 0xfffffffff180ff8f 0xffffffffff180ff8

def z933 : W := mkw 0x24160170a0682863 0x024160170a068286 0xbe1e31f0f078e07e 0xfbe1e31f0f078e07

def z934 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9ffdffff00000005 0x49ffdffff0000000

def z935 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe03a00ff80ff88 0xd6fe03a00ff80ff8

def z936 : W := mkw 0x0b2028005b00d504 0x00b2028005b00d50 0x6fe03800ff80ff8d 0xf6fe03800ff80ff8

def z937 : W := mkw 0x84db95aa00000000 0x084db95aa0000000 0x91dff1ff00000002 0x491dff1ff0000000

def z938 : W := mkw 0x20044055a0fb2af3 0x420044055a0fb2af 0x00000000007f0070 0x000000000007f007

def z939 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x6fffc000ffff1f8b 0xf6fffc000ffff1f8

def z940 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9ffffffff000000f 0xf9ffffffff000000

def z941 : W := mkw 0x90cd16ce86456656 0x890cd16ce8645665 0xf1dd37cf8e47e67f 0x6f1dd37cf8e47e67

def z942 : W := mkw 0x8ffbbfaa49000000 0x08ffbbfaa4900000 0xffffffffff801f8f 0xfffffffffff801f8

def z943 : W := mkw 0x8b603faa5b00d504 0x08b603faa5b00d50 0xffe3ffffff80ff8f 0xfffe3ffffff80ff8

def z944 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0xefe13e0cff80ff8f 0xfefe13e0cff80ff8

def z945 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fdff5ff00000007 0x69fdff5ff0000000

def z946 : W := mkw 0x12403edd1209fff6 0xc12403edd1209fff 0xb0003fff0000fff4 0x0b0003fff0000fff

def z947 : W := mkw 0x8ffbbfaa59009100 0x08ffbbfaa5900910 0x9fffffff70000007 0xe9fffffff7000000

def z948 : W := mkw 0x8dfb95aa00000000 0x08dfb95aa0000000 0x9ffff5ff00000007 0xe9ffff5ff0000000

def z949 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xbffffffffe00ff87 0xebffffffffe00ff8

def z950 : W := mkw 0xcdbfc202edf60008 0x0cdbfc202edf6000 0x4fffc203ffff000b 0xf4fffc203ffff000

def z951 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x3e1e31c0f078f87a 0xf3e1e31c0f078f87

def z952 : W := mkw 0x6f32eb3079ba9929 0x06f32eb3079ba992 0x0e22ca3071b81980 0x90e22ca3071b8198

def z953 : W := mkw 0x096014005b00d504 0x0096014005b00d50 0x6fe03400ff80ff8d 0xf6fe03400ff80ff8

def z954 : W := mkw 0x8fbbabaa59009100 0x08fbbabaa5900910 0x9e3fcbff71801982 0x99e3fcbff7180198

def z955 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0x9fffffffff80f987 0xf9fffffffff80f98

def z956 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1f3dfcf078f87f 0xfbe1f3dfcf078f87

def z957 : W := mkw 0x8fbba9aa00000000 0x08fbba9aa0000000 0x9ffff9ff00000007 0xe9ffff9ff0000000

def z958 : W := mkw 0x20044055a0fb2af3 0x420044055a0fb2af 0x6000000001ff1ff8 0x16000000001ff1ff

def z959 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4ffc0000ffff0009 0xf4ffc0000ffff000

def z960 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e31f0f078f87a 0x5be1e31f0f078f87

def z961 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffce00ffff000f 0xf4fffce00ffff000

def z962 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4ffdc000ffff0009 0x54ffdc000ffff000

def z963 : W := mkw 0x86dbbdaa00000000 0x086dbbdaa0000000 0x9fdffdff00000007 0xe9fdffdff0000000

def z964 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xbfffffff00001f87 0xebfffffff00001f8

def z965 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xfffffffffe00e60f 0xefffffffffe00e60

def z966 : W := mkw 0x10cd14c886446446 0x810cd14c88644644 0xf1dd31c08e47e07f 0x6f1dd31c08e47e07

def z967 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xdfffffff7f801f87 0xfdfffffff7f801f8

def z968 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x71dd31c08e47e67b 0x671dd31c08e47e67

def z969 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x2fe03e00ff80ff84 0xd2fe03e00ff80ff8

def z970 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9e3fffff00000006 0x89e3fffff0000000

def z971 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xd1dd31cc8e47e07b 0x6d1dd31cc8e47e07

def z972 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xefffc000ffff007f 0xfefffc000ffff007

def z973 : W := mkw 0x04160050a0682862 0x004160050a068286 0xbe1e39f0f078f87e 0xfbe1e39f0f078f87

def z974 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xf03fffff01ff1fff 0xff03fffff01ff1ff

def z975 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xdfffffffff80e00f 0xfdfffffffff80e00

def z976 : W := mkw 0x0920400049920000 0x0092040004992000 0x4fe00000ffff0009 0xf4fe00000ffff000

def z977 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903fc1ff00000003 0xa903fc1ff0000000

def z978 : W := mkw 0x6dbfc160edf6204b 0x06dbfc160edf6204 0x5fffc1c0ffff000b 0xf5fffc1c0ffff000

def z979 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fffcfff00000003 0x89fffcfff0000000

def z980 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xfe3e39f0f1f8f87f 0xffe3e39f0f1f8f87

def z981 : W := mkw 0x8f32ab2200000000 0x08f32ab220000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z982 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xffffffff0000060f 0xeffffffff0000060

def z983 : W := mkw 0x0612293010089820 0x0061229301008982 0xbe1e39f0f078f87e 0xfbe1e39f0f078f87

def z984 : W := mkw 0x092000005b00d504 0x0092000005b00d50 0x6fe00e00ff80ff8d 0xf6fe00e00ff80ff8

def z985 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1fd3fcc8e47e67f 0xef1fd3fcc8e47e67

def z986 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xe023ce3f01ff1ff7 0x0e023ce3f01ff1ff

def z987 : W := mkw 0x869ba9aa00000000 0x0869ba9aa0000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z988 : W := mkw 0x0412012000000000 0x0041201200000000 0x901fc1ff00000002 0x0901fc1ff0000000

def z989 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x91ffffff00000007 0x091ffffff0000000

def z990 : W := mkw 0x0920001549090ab0 0x40920001549090ab 0xefe00e3fff801ffd 0xfefe00e3fff801ff

def z991 : W := mkw 0x228d2970944cb863 0x0228d2970944cb86 0xf1dd39f08e47f87f 0x6f1dd39f08e47f87

def z992 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x9e3fc1ff00000002 0x89e3fc1ff0000000

def z993 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffc600ffff078b 0xf4fffc600ffff078

def z994 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0xfffc3fc0ff80ff8f 0xffffc3fc0ff80ff8

def z995 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xdfffffff0180000f 0xfdfffffff0180000

def z996 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x9fffcfff00000007 0xe9fffcfff0000000

def z997 : W := mkw 0x8ffbbfaa02004404 0x08ffbbfaa0200440 0xffffffff8f80ff8f 0xfffffffff8f80ff8

def z998 : W := mkw 0x8ffbbfaa04040000 0x08ffbbfaa0404000 0xdfffffff0e070007 0xedfffffff0e07000

def z999 : W := mkw 0x26162970b46cb863 0x026162970b46cb86 0xfe1e39f0fe7ff87e 0xffe1e39f0fe7ff87

def z1000 : W := mkw 0x0dfb948800000000 0x00dfb94880000000 0x9fffffff00000007 0xe9fffffff0000000

def z1001 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd35cc8e07e675 0x4f1dd35cc8e07e67

def z1002 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0fffc000ffff0002 0xd0fffc000ffff000

def z1003 : W := mkw 0x8dbb81aa49000000 0x08dbb81aa4900000 0xdfffc1ffff80000b 0xfdfffc1ffff80000

def z1004 : W := mkw 0x0d364000e9f20000 0x00d364000e9f2000 0x4fffc000ffff000b 0xf4fffc000ffff000

def z1005 : W := mkw 0x00c9148800000000 0x000c914880000000 0x91dff5ff00000007 0x691dff5ff0000000

def z1006 : W := mkw 0x02403e151209dfb4 0x402403e151209dfb 0x20003e000000fff4 0x020003e000000fff

def z1007 : W := mkw 0x00cd14c884442042 0x000cd14c88444204 0xf1dd35cc8e47e07f 0x6f1dd35cc8e47e07

def z1008 : W := mkw 0xd9e9d68e4f97461c 0x8d9e9d68e4f97461 0x41e1c60f0f870601 0x041e1c60f0f87060

def z1009 : W := mkw 0x60044055fdffbafb 0x460044055fdffbaf 0x60000000fffffff8 0x160000000fffffff

def z1010 : W := mkw 0x649fc175a4ff2afb 0x4649fc175a4ff2af 0x901fc1ff007f0072 0x0901fc1ff007f007

def z1011 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xffdd35ccfe47e67f 0xfffdd35ccfe47e67

def z1012 : W := mkw 0x8ffbbfaa4b004504 0x08ffbbfaa4b00450 0x9fffffff0e000007 0xe9fffffff0e00000

def z1013 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x0fdfc000fe7f000a 0xf0fdfc000fe7f000

def z1014 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0xcfffc830ffff000f 0xfcfffc830ffff000

def z1015 : W := mkw 0x869ba9aa00000000 0x0869ba9aa0000000 0x9e1ff1ff00000002 0x49e1ff1ff0000000

def z1016 : W := mkw 0x8ffbbfaa4b004504 0x08ffbbfaa4b00450 0xdfffffffff80078f 0xfdfffffffff80078

def z1017 : W := mkw 0xcdbfc1aaedf60008 0x0cdbfc1aaedf6000 0xdfffcfffffff000f 0xfdfffcfffffff000

def z1018 : W := mkw 0x1044545586df6ef6 0xc1044545586df6ef 0x61e03e008ffffffd 0xf61e03e008ffffff

def z1019 : W := mkw 0x49244000edf60008 0x049244000edf6000 0x4fc00000ffff0008 0x54fc00000ffff000

def z1020 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4ffec000ffff0008 0xd4ffec000ffff000

def z1021 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e39f07078f876 0x9be1e39f07078f87

def z1022 : W := mkw 0x261229703028b863 0x0261229703028b86 0xbe1e39f07038f876 0xfbe1e39f07038f87

def z1023 : W := mkw 0x32403dfd1209fef7 0xc32403dfd1209fef 0xb0003fff0000fff4 0x0b0003fff0000fff

def z1024 : W := mkw 0xef32eb3279ba9829 0x0ef32eb3279ba982 0x0e22ca3371b81800 0x90e22ca3371b8180

def z1025 : W := mkw 0x8b603e8a5b00d504 0x08b603e8a5b00d50 0x6fe03e0fff80ff8d 0xf6fe03e0fff80ff8

def z1026 : W := mkw 0x1b647e55dfdffff6 0xc1b647e55dfdffff 0x6fe03e00fffffffd 0xf6fe03e00fffffff

def z1027 : W := mkw 0x4dbfc040edf6204a 0x04dbfc040edf6204 0x6fffc000ffffe07b 0xf6fffc000ffffe07

def z1028 : W := mkw 0x10044055dfdffff6 0xc10044055dfdffff 0x60000000fffffff8 0x160000000fffffff

def z1029 : W := mkw 0x8ffbbfaa10009000 0x08ffbbfaa1000900 0xbfffffff0000f807 0xebfffffff0000f80

def z1030 : W := mkw 0x0fbba92000000000 0x00fbba9200000000 0x9fffffff00000007 0xe9fffffff0000000

def z1031 : W := mkw 0x4dbfc001edf60088 0x44dbfc001edf6008 0x4fffc203ffff018b 0xf4fffc203ffff018

def z1032 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0x6023ce3f01ff1ff9 0x96023ce3f01ff1ff

def z1033 : W := mkw 0x8ffbbfaa02004504 0x08ffbbfaa0200450 0x9fffffff00000787 0xe9fffffff0000078

def z1034 : W := mkw 0x10cd14cca6656656 0x810cd14cca665665 0xf1dd35ccfe7fe67f 0x7f1dd35ccfe7fe67

def z1035 : W := mkw 0x4d32c00069b20008 0x04d32c00069b2000 0x4fe3c000ffff000b 0xf4fe3c000ffff000

def z1036 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffc000ffbf0001 0xd4fffc000ffbf000

def z1037 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901fcfff00000006 0x0901fcfff0000000

def z1038 : W := mkw 0x32403ffc1209ff77 0x832403ffc1209ff7 0xb0003ffc0000fff4 0x0b0003ffc0000fff

def z1039 : W := mkw 0x0be93e8800000000 0x00be93e880000000 0x9fffffff00000007 0xe9fffffff0000000

def z1040 : W := mkw 0x020428509048b862 0x0020428509048b86 0xbe1e39f0f078f87e 0xfbe1e39f0f078f87

def z1041 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fc03400ff80ff8d 0x76fc03400ff80ff8

def z1042 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe3ff9f0f078f87f 0xfbe3ff9f0f078f87

def z1043 : W := mkw 0x049f4000a4f60000 0x0049f4000a4f6000 0x4fffc000ffff000b 0xf4fffc000ffff000

def z1044 : W := mkw 0x449fc000a4f60008 0x0449fc000a4f6000 0x4fdfc000fe7f000b 0xf4fdfc000fe7f000

def z1045 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xb1dd31cc8e47e07e 0x6b1dd31cc8e47e07

def z1046 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0xefe23e30ff80ff8f 0xfefe23e30ff80ff8

def z1047 : W := mkw 0x84db95aa02004404 0x084db95aa0200440 0xf1dff5ff8e00e60f 0x6f1dff5ff8e00e60

def z1048 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xbfffffff7180ff87 0xfbfffffff7180ff8

def z1049 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e39f0f038f874 0xdbe1e39f0f038f87

def z1050 : W := mkw 0x26162970b068b863 0x026162970b068b86 0x3e1e39f0f078f878 0xd3e1e39f0f078f87

def z1051 : W := mkw 0x4dbf8000ed640008 0x04dbf8000ed64000 0x4fdf0000fe7f000b 0xf4fdf0000fe7f000

def z1052 : W := mkw 0x8ffbbfaa20200000 0x08ffbbfaa2020000 0x9fffffff70380007 0xf9fffffff7038000

def z1053 : W := mkw 0x86dbbfaa00000000 0x086dbbfaa0000000 0x903fffff00000007 0xa903fffff0000000

def z1054 : W := mkw 0x49a9c0004d960008 0x049a9c0004d96000 0x4fe3c000ffff000b 0xf4fe3c000ffff000

def z1055 : W := mkw 0x2b647e55fbfbfff7 0x42b647e55fbfbfff 0x6fe03e00fffffffd 0xf6fe03e00fffffff

def z1056 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1fd37cc8fc7e7ff 0x6f1fd37cc8fc7e7f

def z1057 : W := mkw 0x0612292000000000 0x0061229200000000 0x9e1ff9ff00000006 0xe9e1ff9ff0000000

def z1058 : W := mkw 0x0089008800000000 0x0008900880000000 0x903fcfff00000007 0xa903fcfff0000000

def z1059 : W := mkw 0x4dbbc0006db60008 0x04dbbc0006db6000 0x4fffc0007fbf0003 0xf4fffc0007fbf000

def z1060 : W := mkw 0x8dfb97aa00000000 0x08dfb97aa0000000 0x91ffcfff00000007 0xa91ffcfff0000000

def z1061 : W := mkw 0x8be9bfaa00000000 0x08be9bfaa0000000 0x91fdffff00000007 0x691fdffff0000000

def z1062 : W := mkw 0x8b603f225b00d504 0x08b603f225b00d50 0x6fe03e33ff80ff8d 0xf6fe03e33ff80ff8

def z1063 : W := mkw 0x19e9568d4f974794 0xc19e9568d4f97479 0x41e1c60f0f870781 0x041e1c60f0f87078

def z1064 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xbe1e3ffff078f87e 0xfbe1e3ffff078f87

def z1065 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fffffff01801987 0xf9fffffff0180198

def z1066 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xbfffffff8000e00f 0xebfffffff8000e00

def z1067 : W := mkw 0x00c9148802004404 0x000c914880200440 0xf1ffffff8f80ff8f 0xff1ffffff8f80ff8

def z1068 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xc023ce3f01ff1ff3 0x9c023ce3f01ff1ff

def z1069 : W := mkw 0x00004015009b0ab0 0x400004015009b0ab 0xa023ce3f01ff1ff6 0x9a023ce3f01ff1ff

def z1070 : W := mkw 0x4dbfc000edf60008 0x04dbfc000edf6000 0x4fffca00ffff198b 0xf4fffca00ffff198

def z1071 : W := mkw 0x549fc0dda4ff2afa 0xc549fc0dda4ff2af 0x901fc1ff007f0072 0x0901fc1ff007f007

def z1072 : W := mkw 0x0004405580db2af2 0x40004405580db2af 0x6000000081fffff8 0x16000000081fffff

def z1073 : W := mkw 0x8ffbbfaa59009100 0x08ffbbfaa5900910 0xdfffffffff80198f 0xfdfffffffff80198

def z1074 : W := mkw 0x20044055fbfbfff7 0x420044055fbfbfff 0x60000000fffffff8 0x160000000fffffff

def z1075 : W := mkw 0x86dbbfaa00000000 0x086dbbfaa0000000 0x901ff1ff00000002 0x0901ff1ff0000000

def z1076 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0xbfffffff0040007f 0xebfffffff0040007

def z1077 : W := mkw 0x26162970b068b863 0x026162970b068b86 0xfe1f39f0f07ff87f 0xffe1f39f0f07ff87

def z1078 : W := mkw 0x8f72bfaa00000000 0x08f72bfaa0000000 0x9e3effff00000006 0xe9e3effff0000000

def z1079 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9ffff7ff00000003 0x49ffff7ff0000000

def z1080 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0x71dd35cc8e47e679 0x471dd35cc8e47e67

def z1081 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901fc9ff00000006 0xa901fc9ff0000000

def z1082 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dc31c08e47e67e 0x6f1dc31c08e47e67

def z1083 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0xefe03e3fff80ff8d 0xfefe03e3fff80ff8

def z1084 : W := mkw 0x8ffbbfaa49000000 0x08ffbbfaa4900000 0x9ffffffffe000007 0xe9ffffffffe00000

def z1085 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xf1dd3dcc8e47fe7f 0xff1dd3dcc8e47fe7

def z1086 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x1fffffff00000001 0xc1fffffff0000000

def z1087 : W := mkw 0x8ffbbfaa1200d504 0x08ffbbfaa1200d50 0x9fffffff0000e007 0xe9fffffff0000e00

def z1088 : W := mkw 0x0b603e005b00d504 0x00b603e005b00d50 0x6fe13e00ffc7ff8f 0xf6fe13e00ffc7ff8

def z1089 : W := mkw 0x50044055efff6efe 0xc50044055efff6ef 0x60000000fffffff8 0x160000000fffffff

def z1090 : W := mkw 0x82c93faa00000000 0x082c93faa0000000 0x91ffffff00000007 0xe91ffffff0000000

def z1091 : W := mkw 0x8ffbbfaa5b00d504 0x08ffbbfaa5b00d50 0xffffffff0f80ff87 0xeffffffff0f80ff8

def z1092 : W := mkw 0x8ffbbfaa00000000 0x08ffbbfaa0000000 0x9fdfffff00000006 0x49fdfffff0000000

def z1093 : W := mkw 0xb2403ffe1209fe77 0x8b2403ffe1209fe7 0xb0003fff0000fe74 0x0b0003fff0000fe7

def z1094 : W := mkw 0x10cd14cc86456656 0x810cd14cc8645665 0xb1dd35cc8e47e676 0x4b1dd35cc8e47e67

def z1095 : W := mkw 0x0b603e885b00d504 0x00b603e885b00d50 0xffe03fccff80ff8d 0xfffe03fccff80ff8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z10,z9]),(0,[z1,z11,z2,z3,z4,z8,z6])],[(1,[z12,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z13,z5,z6]),(0,[z1,z14,z2,z3,z4,z13,z6]),(0,[z1,z15,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z16,z17])],[(0,[z18,z2,z19,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z20,z8,z6]),(0,[z1,z2,z3,z4,z8,z16,z21]),(0,[z1,z22,z2,z3,z4,z8,z6])],[(0,[z0,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z23,z6]),(0,[z1,z2,z3,z24,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z25,z16]),(0,[z1,z26,z3,z4,z8,z10,z6])],[(0,[z27,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z13,z8,z16])],[(1,[z1,z2,z28,z4,z8,z6]),(0,[z29,z1,z2,z3,z4,z8,z30]),(0,[z1,z31,z2,z32,z3,z4,z6])],[(0,[z33,z1,z2,z3,z4,z8,z6]),(0,[z1,z34,z2,z3,z4,z8,z6])],[(0,[z1,z35,z2,z3,z4,z8,z6]),(0,[z1,z2,z36,z3,z4,z8,z6]),(0,[z29,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z37,z8,z6]),(1,[z1,z2,z3,z4,z8,z38]),(0,[z1,z7,z2,z3,z4,z39,z6]),(0,[z1,z2,z3,z4,z8,z6,z40]),(0,[z1,z2,z41,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z42,z6]),(0,[z43,z2,z3,z44,z4,z8,z6]),(0,[z1,z45,z2,z3,z4,z8,z6]),(0,[z1,z46,z2,z3,z4,z8,z16]),(0,[z1,z47,z2,z3,z4,z8,z6])],[(0,[z48,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z49,z4,z8,z6]),(1,[z1,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z4,z8,z51,z6]),(0,[z1,z2,z3,z4,z52,z8,z6]),(0,[z1,z53,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z54,z6]),(0,[z1,z2,z55,z3,z4,z8,z6]),(0,[z1,z56,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z57,z6]),(0,[z0,z1,z58,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z59,z8,z6]),(0,[z1,z2,z3,z4,z60,z8,z6]),(0,[z1,z61,z2,z3,z4,z8,z6])],[(0,[z62,z1,z2,z3,z4,z8,z6]),(0,[z63,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z64,z4,z8,z6]),(0,[z1,z31,z2,z3,z65,z8,z6])],[(1,[z1,z66,z3,z4,z8,z9]),(0,[z1,z67,z2,z3,z4,z8,z9]),(0,[z1,z3,z4,z8,z16,z6,z9]),(0,[z1,z2,z3,z4,z8,z68,z6]),(0,[z69,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z70,z6]),(0,[z1,z2,z3,z4,z71,z8,z6]),(0,[z1,z72,z2,z3,z4,z8,z73]),(0,[z1,z2,z3,z4,z8,z9,z74])],[(0,[z1,z2,z75,z3,z4,z8,z16]),(0,[z1,z76,z2,z77,z4,z8,z6])],[(0,[z1,z2,z3,z44,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z78]),(0,[z1,z2,z3,z79,z4,z8,z6]),(0,[z1,z76,z2,z4,z80,z8,z6]),(0,[z1,z2,z3,z81,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z82])]],
   [[(0,[z83,z1,z2,z3,z44,z8,z6]),(0,[z1,z2,z3,z4,z84,z8,z6]),(0,[z1,z2,z3,z4,z85,z8,z6]),(0,[z1,z2,z32,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z13,z8,z10])],[(0,[z1,z2,z3,z4,z8,z86,z6]),(0,[z1,z2,z3,z87,z4,z8,z6]),(0,[z1,z2,z3,z88,z4,z8,z6]),(0,[z1,z2,z3,z89,z4,z8,z6]),(1,[z1,z2,z3,z4,z90,z6])],[],[(0,[z1,z91,z2,z3,z4,z8,z6]),(1,[z92,z2,z3,z4,z8,z93]),(0,[z1,z94,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z95,z8,z6]),(0,[z1,z2,z96,z3,z4,z8,z6])],[(0,[z92,z1,z46,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z97,z6])],[(0,[z1,z2,z98,z3,z4,z8,z6]),(0,[z1,z99,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z65,z100,z6]),(0,[z1,z2,z3,z4,z8,z101,z6])],[(0,[z1,z102,z2,z3,z4,z8,z16]),(0,[z103,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z104,z3,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z105,z6]),(0,[z1,z2,z3,z4,z100,z8,z6]),(0,[z1,z2,z3,z4,z106,z8,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z1,z107,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z108,z4,z8,z6]),(0,[z1,z109,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z110,z8,z6]),(0,[z1,z111,z2,z3,z4,z8,z6]),(1,[z43,z2,z3,z44,z8,z6]),(0,[z1,z2,z3,z4,z112,z8,z9]),(0,[z1,z2,z3,z4,z39,z25,z6]),(0,[z1,z2,z3,z4,z13,z8,z6])],[(1,[z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z113,z6]),(0,[z1,z2,z114,z3,z115,z4,z8]),(0,[z1,z2,z3,z4,z116,z8,z6]),(0,[z117,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z118,z4,z8,z6]),(0,[z1,z2,z3,z119,z4,z8,z6]),(0,[z1,z120,z2,z3,z4,z8,z6])],[(0,[z1,z121,z2,z3,z4,z8,z6])],[(0,[z1,z122,z2,z3,z4,z8,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z1,z72,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z123,z6]),(0,[z1,z2,z3,z4,z8,z16,z124]),(0,[z1,z2,z77,z3,z100,z8,z6]),(0,[z1,z46,z2,z3,z4,z8,z6]),(0,[z1,z2,z125,z3,z4,z8,z10])],[(1,[z1,z14,z3,z4,z8,z9]),(0,[z1,z3,z4,z112,z8,z6,z9]),(0,[z1,z2,z3,z4,z8,z126,z6]),(0,[z1,z2,z3,z4,z8,z6,z127]),(0,[z1,z2,z3,z128,z4,z8,z6]),(0,[z1,z2,z129,z3,z4,z8,z6]),(1,[z1,z3,z4,z8,z130,z6])],[(0,[z1,z2,z3,z4,z8,z6,z131]),(1,[z1,z2,z3,z8,z132,z6])]],
   [[(0,[z48,z1,z2,z3,z133,z8,z6]),(0,[z12,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z134,z9]),(0,[z1,z2,z3,z4,z8,z135,z9]),(0,[z1,z2,z3,z4,z8,z136,z6])],[(0,[z137,z1,z2,z3,z4,z8,z6]),(0,[z1,z138,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z139,z6]),(0,[z1,z2,z3,z140,z4,z8,z6]),(0,[z1,z14,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z141,z8,z6])],[(0,[z142,z1,z2,z115,z4,z8,z6]),(0,[z2,z3,z44,z4,z143,z8,z6]),(0,[z1,z2,z3,z4,z8,z144,z6]),(0,[z145,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z146,z8,z6])],[(0,[z1,z2,z3,z4,z8,z147,z6]),(0,[z43,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z148,z9]),(0,[z1,z2,z3,z4,z8,z16,z30]),(0,[z1,z149,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z150,z4,z8,z6]),(0,[z1,z2,z3,z4,z151,z8,z6]),(0,[z1,z2,z3,z152,z4,z8,z6])],[(0,[z1,z2,z153,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z154,z6]),(1,[z1,z72,z3,z155,z8,z6]),(0,[z1,z31,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z156,z6]),(0,[z1,z2,z3,z4,z8,z157,z6])],[(0,[z1,z66,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z16,z9]),(0,[z1,z2,z3,z4,z8,z158,z6]),(0,[z159,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z32,z4,z160,z6]),(0,[z1,z2,z3,z4,z8,z161,z6]),(0,[z1,z2,z3,z100,z8,z25,z6])],[(0,[z1,z2,z3,z162,z4,z8,z6]),(0,[z43,z1,z2,z3,z143,z8,z6]),(0,[z163,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z125,z3,z4,z8,z6])],[(0,[z164,z1,z2,z3,z4,z8,z6]),(0,[z142,z18,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z165,z4,z8,z6]),(0,[z12,z1,z58,z2,z3,z4,z6]),(0,[z1,z2,z166,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z167,z16])]],
   [[(1,[z1,z2,z3,z4,z168,z6]),(0,[z1,z2,z3,z4,z169,z8,z6]),(0,[z1,z170,z2,z3,z4,z8,z6])],[(0,[z171,z1,z2,z3,z4,z8,z6]),(0,[z172,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z44,z155,z8,z6]),(0,[z1,z2,z173,z3,z4,z8,z6]),(1,[z1,z174,z3,z4,z8,z6]),(0,[z175,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z176,z3,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z177,z8,z6])],[(1,[z1,z2,z114,z3,z4,z8]),(0,[z1,z2,z3,z4,z178,z8,z6]),(0,[z29,z1,z179,z2,z3,z4,z8]),(0,[z180,z1,z2,z3,z4,z8,z6]),(0,[z181,z1,z2,z3,z4,z8,z16]),(0,[z1,z31,z2,z77,z3,z8,z6]),(0,[z1,z2,z3,z4,z182,z8,z6]),(0,[z1,z2,z125,z3,z4,z6,z183])],[(0,[z1,z2,z184,z3,z4,z8,z6]),(0,[z1,z102,z2,z3,z4,z8,z6]),(0,[z1,z2,z77,z3,z4,z8,z16])],[(1,[z1,z2,z3,z4,z8,z185]),(0,[z1,z186,z2,z187,z3,z4,z6]),(0,[z1,z2,z3,z188,z4,z8,z6]),(0,[z1,z2,z189,z3,z4,z8,z6])],[(0,[z1,z2,z187,z3,z4,z8,z6]),(0,[z1,z2,z75,z115,z4,z8,z6]),(0,[z1,z190,z2,z3,z4,z8,z6]),(0,[z1,z14,z2,z3,z4,z167,z6]),(0,[z1,z2,z3,z4,z191,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z192])],[(0,[z1,z2,z3,z115,z4,z8,z16]),(0,[z1,z2,z3,z4,z193,z8,z6]),(0,[z1,z14,z3,z4,z8,z167,z6]),(0,[z1,z2,z3,z4,z8,z194,z6]),(0,[z1,z195,z2,z3,z4,z8,z6])],[(0,[z196,z1,z2,z3,z4,z8,z16]),(0,[z1,z197,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z155,z8,z9]),(0,[z1,z2,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z198])]],
   [[(0,[z1,z2,z3,z4,z8,z199,z16]),(0,[z1,z2,z3,z4,z10,z6,z183])],[(0,[z200,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z98,z19,z4,z8,z6]),(1,[z1,z201,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z16,z202]),(0,[z1,z2,z3,z4,z8,z203,z6]),(0,[z1,z204,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z93,z9]),(0,[z1,z72,z2,z3,z4,z8,z6]),(0,[z1,z72,z3,z4,z155,z8,z6]),(0,[z1,z201,z2,z3,z4,z8,z9]),(0,[z1,z26,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z205])],[(0,[z1,z2,z3,z4,z206,z8,z6]),(0,[z1,z2,z4,z160,z8,z39,z6]),(0,[z1,z2,z3,z4,z8,z207,z6]),(0,[z1,z2,z3,z4,z8,z6,z208]),(0,[z1,z2,z3,z4,z8,z209,z6])],[(0,[z1,z2,z3,z4,z210,z8,z6]),(0,[z1,z2,z3,z4,z8,z211,z6]),(0,[z1,z212,z2,z3,z4,z8,z213]),(0,[z1,z214,z2,z3,z4,z8,z6]),(0,[z1,z2,z215,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z216,z8,z6])],[(0,[z83,z2,z3,z4,z143,z8,z6]),(0,[z29,z1,z2,z75,z3,z4,z8]),(0,[z217,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z218]),(1,[z1,z7,z2,z4,z39,z6])],[(0,[z1,z98,z3,z89,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z219,z6]),(0,[z1,z2,z3,z4,z220,z8,z6]),(0,[z221,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z222,z6]),(0,[z1,z2,z3,z4,z223,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z6,z224]),(0,[z1,z46,z2,z3,z4,z8,z134]),(0,[z1,z2,z75,z4,z8,z134,z6])],[(1,[z0,z2,z3,z4,z148,z6]),(0,[z1,z2,z3,z4,z8,z16,z183])],[(0,[z1,z2,z3,z4,z8,z6,z225]),(0,[z1,z2,z3,z4,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z226]),(0,[z181,z1,z14,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z160,z8,z6])],[(0,[z48,z1,z2,z3,z4,z50,z6]),(0,[z227,z1,z2,z3,z4,z8,z6]),(0,[z1,z228,z2,z3,z4,z80,z6]),(0,[z1,z2,z3,z4,z8,z6,z229]),(0,[z1,z2,z3,z4,z8,z6,z230]),(0,[z1,z2,z32,z3,z4,z160,z6])],[(0,[z1,z2,z3,z4,z8,z231,z6]),(0,[z1,z2,z3,z4,z232,z8,z6]),(0,[z1,z2,z3,z4,z8,z233,z6]),(0,[z1,z2,z3,z4,z8,z167,z6]),(0,[z1,z234,z2,z3,z4,z8,z6]),(0,[z1,z235,z2,z3,z4,z8,z16]),(1,[z1,z2,z75,z4,z8,z134])],[(0,[z1,z2,z236,z3,z4,z8,z6]),(0,[z29,z1,z2,z3,z237,z8,z6]),(0,[z1,z2,z3,z4,z80,z8,z9]),(0,[z1,z2,z238,z3,z4,z8,z6]),(1,[z1,z46,z2,z4,z8,z202]),(1,[z1,z2,z3,z4,z13,z10])],[(0,[z18,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z239,z8,z6]),(0,[z1,z2,z3,z4,z8,z213,z6]),(0,[z1,z2,z3,z4,z8,z16,z135]),(0,[z1,z46,z2,z4,z8,z6,z202]),(0,[z1,z2,z75,z3,z4,z8,z134])],[(0,[z1,z2,z3,z4,z8,z6,z240])]],
   [[(0,[z1,z2,z3,z4,z8,z241,z6]),(0,[z1,z242,z2,z3,z4,z8,z6]),(1,[z142,z2,z115,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z9]),(0,[z1,z2,z3,z4,z8,z9,z131])],[(1,[z1,z243,z3,z4,z8,z6]),(0,[z244,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z245,z6]),(0,[z1,z246,z2,z3,z4,z8,z6])],[(0,[z48,z1,z2,z3,z4,z247,z6]),(0,[z1,z2,z248,z3,z4,z8,z6]),(1,[z1,z249,z89,z4,z8,z6]),(0,[z250,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z251,z6])],[(0,[z1,z2,z3,z115,z4,z8,z6]),(0,[z252,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z253,z4,z8,z6]),(0,[z1,z254,z2,z3,z4,z8,z6])],[(0,[z196,z1,z2,z3,z4,z8,z6]),(0,[z255,z1,z2,z3,z4,z8,z6]),(0,[z1,z249,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z256,z8,z6]),(0,[z1,z2,z257,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z258]),(0,[z1,z259,z2,z3,z4,z8,z6])],[(0,[z1,z2,z260,z3,z4,z8,z6]),(0,[z1,z2,z3,z44,z8,z6,z261]),(0,[z1,z2,z3,z4,z8,z6,z6]),(0,[z1,z2,z3,z4,z8,z199,z6]),(0,[z1,z2,z3,z4,z8,z262,z16]),(0,[z1,z263,z2,z3,z4,z8,z6])],[(0,[z142,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z264,z8,z6])],[(0,[z1,z2,z3,z4,z265,z8,z6]),(0,[z1,z2,z4,z8,z134,z6,z202]),(0,[z266,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z267,z6]),(0,[z83,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z5,z167,z6]),(0,[z1,z2,z3,z268,z4,z8,z6]),(0,[z1,z2,z3,z4,z269,z8,z16]),(0,[z1,z270,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z271])],[(0,[z272,z1,z2,z3,z4,z8,z6]),(0,[z1,z273,z2,z3,z4,z8,z6]),(0,[z1,z2,z274,z3,z4,z8,z6])],[(0,[z1,z2,z3,z275,z4,z8,z6]),(0,[z1,z276,z2,z3,z4,z8,z6]),(0,[z1,z2,z19,z3,z4,z8,z16]),(0,[z277,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z278,z6])],[(0,[z83,z1,z2,z3,z143,z8,z6])],[(1,[z1,z2,z279,z4,z8,z6]),(0,[z1,z2,z280,z3,z4,z8,z6]),(0,[z281,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z282,z4,z8,z6])],[(0,[z1,z2,z114,z3,z4,z8,z6]),(0,[z181,z1,z201,z3,z4,z8,z6]),(0,[z1,z15,z2,z3,z4,z8,z9]),(0,[z1,z2,z283,z3,z4,z8,z6]),(0,[z284,z1,z2,z3,z4,z8,z6])],[(0,[z285,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z286,z3,z4,z8,z6]),(0,[z0,z1,z2,z3,z4,z148,z6]),(0,[z0,z1,z14,z2,z3,z4,z6]),(0,[z1,z249,z212,z3,z4,z8,z6])],[(0,[z287,z1,z2,z3,z4,z8,z6]),(0,[z142,z2,z3,z115,z4,z8,z6]),(0,[z288,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z13,z148,z6]),(0,[z1,z2,z3,z24,z4,z8,z9]),(0,[z1,z31,z2,z3,z4,z25,z6])]],
   [[(0,[z1,z212,z2,z3,z4,z8,z16]),(1,[z1,z3,z4,z112,z8,z9]),(0,[z1,z2,z3,z4,z8,z16,z261]),(0,[z1,z2,z3,z4,z289,z8,z6])],[(0,[z1,z2,z3,z4,z133,z8,z6]),(0,[z1,z2,z3,z4,z247,z8,z6]),(0,[z18,z1,z2,z19,z4,z8,z6]),(0,[z1,z2,z3,z290,z44,z8,z6]),(0,[z1,z2,z3,z4,z8,z291,z6]),(0,[z1,z235,z2,z3,z4,z8,z6]),(0,[z1,z76,z2,z3,z80,z8,z6]),(0,[z1,z2,z3,z290,z8,z135,z6])],[(0,[z1,z2,z3,z4,z8,z6,z292]),(0,[z1,z2,z3,z4,z269,z16,z6]),(0,[z1,z2,z125,z3,z4,z13,z6])],[(1,[z1,z2,z3,z4,z247,z6]),(0,[z1,z2,z3,z4,z8,z6,z293]),(0,[z1,z2,z3,z4,z8,z6,z294]),(0,[z1,z2,z3,z4,z295,z8,z6])],[(0,[z1,z2,z3,z296,z4,z8,z6]),(0,[z1,z2,z297,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z298,z8,z6]),(0,[z1,z2,z3,z4,z8,z299,z6]),(0,[z1,z300,z2,z3,z4,z8,z6])],[(0,[z301,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z8,z16])],[(0,[z1,z302,z2,z3,z115,z4,z8]),(0,[z1,z2,z3,z303,z4,z8,z6]),(1,[z1,z2,z3,z4,z304,z6]),(0,[z1,z2,z3,z4,z8,z305,z16]),(0,[z1,z2,z3,z306,z4,z8,z16]),(0,[z1,z179,z2,z3,z4,z8,z261])],[(0,[z1,z307,z2,z3,z4,z8,z6]),(0,[z308,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z309,z4,z8,z16]),(1,[z1,z2,z77,z306,z8,z6]),(0,[z1,z2,z3,z310,z4,z8,z6]),(0,[z1,z2,z3,z4,z311,z8,z6])]],
   [[(0,[z1,z312,z2,z187,z3,z4,z6]),(0,[z1,z2,z313,z3,z4,z8,z6]),(0,[z1,z76,z2,z4,z160,z8,z6])],[(0,[z1,z2,z3,z4,z8,z314,z6]),(0,[z29,z1,z2,z3,z4,z8,z93]),(0,[z1,z2,z315,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z316]),(1,[z1,z58,z3,z4,z112,z6]),(0,[z1,z2,z317,z3,z4,z8,z6]),(0,[z1,z7,z31,z2,z3,z4,z6])],[(0,[z1,z2,z3,z318,z4,z8,z6]),(0,[z319,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z320,z8,z6]),(0,[z1,z2,z3,z4,z8,z262,z6]),(0,[z321,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z143,z8,z9]),(0,[z1,z322,z2,z3,z4,z8,z6]),(0,[z1,z102,z2,z3,z4,z8,z38]),(0,[z1,z2,z3,z4,z8,z6,z323]),(0,[z1,z2,z324,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z25,z6]),(0,[z1,z2,z3,z4,z8,z6,z325])],[(0,[z1,z187,z3,z4,z8,z6,z9]),(0,[z1,z2,z326,z3,z4,z8,z6]),(1,[z1,z3,z4,z8,z16,z9]),(0,[z1,z7,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z10,z16])],[(0,[z1,z2,z327,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z328,z8,z6]),(0,[z0,z2,z3,z4,z8,z148,z6]),(0,[z1,z2,z3,z4,z329,z8,z6]),(0,[z1,z2,z3,z4,z269,z8,z6]),(0,[z1,z31,z2,z3,z4,z100,z6]),(0,[z1,z2,z3,z4,z330,z8,z6])],[(0,[z48,z1,z2,z3,z4,z8,z185]),(0,[z1,z2,z3,z4,z331,z8,z6]),(0,[z332,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z333,z8,z6]),(0,[z1,z2,z3,z4,z334,z80,z6])],[(0,[z2,z3,z4,z5,z8,z148,z6]),(0,[z1,z2,z3,z4,z335,z8,z6]),(0,[z336,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z337,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z338]),(0,[z339,z1,z2,z3,z4,z8,z6]),(0,[z340,z1,z2,z3,z4,z8,z6])],[(0,[z1,z341,z2,z3,z4,z8,z6]),(0,[z12,z0,z2,z3,z4,z8,z6]),(0,[z1,z2,z98,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z218]),(0,[z1,z342,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z343,z4,z8,z6]),(0,[z1,z179,z2,z3,z8,z6,z261])],[(0,[z92,z1,z2,z3,z4,z8,z30]),(0,[z1,z344,z2,z3,z4,z8,z6])],[(0,[z1,z345,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z346]),(0,[z29,z1,z2,z28,z4,z8,z6]),(0,[z29,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z347,z4,z8,z6]),(0,[z1,z2,z3,z4,z100,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z348])],[(0,[z0,z1,z2,z3,z4,z8,z9]),(0,[z349,z1,z2,z3,z4,z8,z6]),(0,[z92,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z350,z6]),(0,[z1,z2,z3,z4,z8,z351,z6]),(0,[z352,z1,z2,z3,z4,z8,z6])],[(0,[z1,z212,z2,z3,z4,z8,z6]),(0,[z1,z353,z2,z3,z4,z8,z6]),(0,[z1,z2,z354,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z9,z258]),(0,[z1,z2,z3,z4,z13,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z355])],[(0,[z1,z356,z2,z3,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z167,z6]),(1,[z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z75,z3,z4,z8,z6])],[(0,[z1,z357,z2,z3,z4,z8,z6]),(0,[z1,z2,z115,z4,z8,z6,z202]),(0,[z1,z2,z3,z4,z8,z358,z6]),(0,[z359,z1,z2,z3,z4,z8,z6]),(0,[z1,z46,z2,z75,z4,z8,z6]),(0,[z360,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z361,z2,z3,z4,z8,z6]),(0,[z1,z2,z306,z4,z80,z8,z6]),(0,[z1,z2,z32,z3,z4,z8,z6]),(0,[z362,z1,z2,z3,z4,z8,z6])],[(0,[z363,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z364]),(0,[z1,z2,z3,z365,z4,z8,z6]),(0,[z1,z249,z3,z89,z4,z8,z6])],[(0,[z1,z58,z2,z3,z4,z8,z366]),(0,[z367,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z368,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z126,z9]),(0,[z1,z2,z3,z4,z100,z39,z6])],[(0,[z66,z2,z187,z3,z4,z8,z6]),(0,[z369,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z370,z6]),(0,[z1,z2,z371,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z168,z8,z6]),(0,[z1,z372,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z373,z6])],[(0,[z92,z2,z3,z4,z8,z93,z6]),(0,[z1,z2,z3,z309,z4,z8,z6]),(0,[z1,z2,z3,z374,z4,z8,z6]),(0,[z181,z1,z3,z4,z112,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z375]),(0,[z1,z2,z3,z376,z4,z8,z6])],[(1,[z1,z14,z3,z4,z167,z6]),(0,[z1,z2,z3,z4,z8,z6,z17]),(0,[z1,z377,z2,z3,z4,z8,z6])],[(0,[z378,z1,z2,z3,z4,z8,z6]),(0,[z1,z179,z2,z3,z4,z8,z9]),(0,[z1,z379,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z6,z21])],[(0,[z1,z66,z2,z3,z4,z8,z70]),(0,[z380,z1,z2,z3,z4,z8,z6]),(0,[z381,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z382,z8,z6])]],
   [[(0,[z383,z1,z2,z3,z4,z8,z6]),(0,[z1,z384,z2,z3,z4,z8,z6]),(0,[z1,z385,z2,z3,z8,z39,z6])],[(1,[z1,z2,z3,z4,z8,z386]),(0,[z1,z2,z3,z4,z8,z6,z387]),(0,[z1,z2,z3,z4,z8,z6,z388]),(0,[z1,z389,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z290,z4,z8,z261]),(0,[z1,z2,z3,z4,z8,z10,z6])],[(0,[z1,z2,z3,z4,z390,z8,z6]),(0,[z1,z2,z3,z4,z112,z5,z6]),(0,[z1,z2,z3,z391,z4,z8,z6]),(0,[z1,z102,z2,z3,z309,z8,z6]),(0,[z1,z2,z125,z3,z4,z8,z9]),(0,[z1,z2,z77,z306,z4,z8,z6])],[(1,[z196,z66,z3,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z8,z16]),(0,[z1,z2,z166,z3,z4,z8,z9]),(0,[z1,z392,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z393,z6]),(0,[z1,z2,z3,z4,z8,z394,z6])],[(0,[z1,z2,z395,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z38]),(0,[z1,z2,z3,z4,z112,z8,z16]),(0,[z1,z2,z3,z4,z8,z396,z16])],[(0,[z1,z2,z3,z397,z4,z8,z6]),(0,[z398,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z399,z6]),(0,[z1,z400,z2,z3,z4,z8,z6]),(0,[z1,z401,z2,z3,z4,z8,z6])],[(0,[z1,z2,z28,z3,z4,z8,z6]),(1,[z29,z2,z3,z4,z8,z30]),(0,[z1,z2,z3,z4,z8,z16,z93]),(0,[z1,z72,z102,z3,z4,z8,z6]),(0,[z1,z102,z2,z3,z4,z8,z9]),(0,[z1,z76,z2,z3,z100,z8,z6])]],
   [[(0,[z12,z1,z2,z3,z4,z8,z6]),(0,[z29,z1,z2,z3,z4,z8,z6]),(0,[z181,z1,z3,z4,z8,z16,z6]),(0,[z1,z2,z32,z3,z4,z39,z6]),(0,[z1,z2,z402,z3,z4,z8,z6])],[(0,[z1,z2,z187,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z403,z6]),(0,[z1,z72,z2,z3,z309,z8,z6]),(0,[z404,z1,z2,z3,z4,z8,z6]),(0,[z1,z405,z2,z3,z4,z8,z6]),(0,[z1,z2,z406,z3,z4,z8,z16]),(0,[z1,z407,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z408,z8,z6]),(0,[z1,z2,z3,z4,z13,z8,z183])],[(0,[z1,z2,z409,z3,z4,z8,z6]),(0,[z1,z2,z3,z410,z4,z8,z6]),(0,[z1,z2,z3,z411,z4,z8,z6]),(0,[z1,z412,z2,z3,z4,z8,z6])],[(0,[z1,z413,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z16,z21]),(0,[z1,z2,z3,z4,z8,z6,z414])],[(0,[z1,z2,z3,z3,z4,z8,z6]),(0,[z415,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z8,z132,z39,z6])],[(1,[z1,z2,z104,z4,z8,z6]),(0,[z1,z416,z2,z3,z4,z8,z6]),(0,[z1,z14,z2,z3,z4,z8,z16]),(0,[z1,z67,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z417,z8,z6]),(0,[z1,z418,z2,z3,z4,z8,z6])],[(0,[z1,z186,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z419,z4,z8,z6]),(0,[z29,z1,z2,z3,z290,z4,z8]),(0,[z1,z72,z2,z3,z4,z8,z9]),(0,[z420,z1,z2,z3,z4,z8,z6])],[(0,[z43,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z148,z16]),(0,[z1,z421,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z422]),(0,[z1,z3,z309,z4,z155,z8,z6]),(0,[z1,z2,z423,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z424,z8,z6]),(0,[z1,z2,z19,z4,z8,z6,z202]),(0,[z1,z31,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z16,z6,z21]),(0,[z1,z2,z3,z425,z4,z8,z6]),(0,[z1,z2,z3,z426,z4,z8,z6])],[(0,[z1,z66,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z427,z8,z6]),(0,[z1,z2,z3,z65,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z16,z16])],[(0,[z1,z14,z2,z3,z4,z8,z428]),(0,[z181,z1,z2,z3,z4,z8,z6]),(0,[z429,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z132,z6])],[(0,[z1,z2,z3,z4,z148,z167,z6]),(0,[z1,z379,z2,z3,z4,z8,z6]),(0,[z1,z430,z2,z3,z4,z8,z6]),(0,[z1,z58,z14,z3,z4,z8,z6]),(0,[z1,z14,z3,z4,z8,z6,z9]),(0,[z1,z2,z77,z3,z4,z8,z6]),(0,[z431,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z432,z8,z6]),(0,[z1,z2,z3,z4,z8,z433,z6])],[(0,[z1,z2,z3,z4,z8,z6,z434]),(0,[z435,z1,z2,z3,z4,z8,z6]),(0,[z1,z249,z2,z98,z4,z8,z6]),(0,[z1,z436,z2,z3,z4,z8,z6]),(0,[z1,z437,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z438,z9]),(0,[z1,z439,z2,z3,z4,z8,z6])],[(0,[z1,z440,z2,z3,z4,z8,z6]),(0,[z441,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z442,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z443,z6]),(0,[z1,z2,z3,z4,z8,z6,z444])],[(0,[z1,z2,z3,z4,z160,z8,z9]),(1,[z1,z2,z3,z4,z269,z16]),(0,[z1,z2,z125,z3,z4,z8,z183])],[(0,[z1,z66,z3,z4,z8,z6,z9]),(0,[z29,z1,z174,z3,z4,z8,z6]),(0,[z92,z1,z179,z2,z3,z4,z8]),(0,[z1,z2,z445,z3,z4,z8,z6]),(0,[z1,z7,z2,z3,z4,z160,z6]),(0,[z1,z2,z3,z446,z4,z8,z6]),(0,[z1,z179,z2,z3,z4,z8,z135]),(0,[z1,z2,z3,z4,z8,z6,z447])]],
   [[(1,[z1,z186,z2,z3,z4,z6]),(0,[z1,z2,z448,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z167,z9])],[(0,[z1,z302,z2,z3,z4,z8,z6]),(0,[z1,z449,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z290,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z124]),(0,[z1,z2,z450,z3,z4,z8,z6])],[(0,[z1,z451,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z452,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z396,z6]),(0,[z1,z2,z3,z4,z112,z8,z6]),(0,[z1,z2,z453,z3,z4,z8,z6])],[(0,[z196,z66,z2,z3,z4,z8,z6]),(0,[z1,z66,z2,z3,z4,z8,z225]),(0,[z1,z2,z3,z4,z454,z8,z6]),(0,[z1,z2,z3,z4,z155,z8,z16]),(0,[z1,z2,z2,z3,z4,z8,z16])],[(0,[z1,z2,z3,z290,z143,z8,z6])],[(0,[z1,z249,z2,z89,z4,z8,z6])],[(0,[z196,z1,z187,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z455,z8,z6]),(0,[z1,z201,z2,z3,z4,z8,z16]),(0,[z1,z456,z2,z3,z4,z8,z6]),(0,[z1,z2,z457,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z458,z6]),(0,[z1,z2,z3,z4,z8,z6,z30]),(0,[z1,z2,z77,z3,z306,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z50,z6]),(0,[z1,z2,z3,z4,z8,z459,z6])],[(0,[z1,z2,z3,z143,z155,z8,z6]),(0,[z29,z1,z2,z3,z296,z8,z6]),(0,[z1,z72,z2,z3,z4,z8,z218]),(0,[z1,z102,z2,z3,z155,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z9]),(0,[z1,z2,z3,z460,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z134,z6]),(0,[z1,z2,z3,z4,z461,z8,z6]),(0,[z1,z2,z3,z4,z8,z135,z6]),(0,[z1,z462,z2,z3,z4,z8,z6])],[(0,[z1,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z463,z4,z8,z6]),(0,[z1,z14,z2,z3,z4,z8,z6]),(1,[z1,z2,z4,z8,z222,z6]),(0,[z1,z2,z3,z4,z8,z464,z6]),(0,[z1,z179,z2,z3,z290,z8,z6])],[(0,[z1,z465,z2,z3,z4,z143,z8]),(0,[z12,z2,z3,z4,z5,z8,z6]),(0,[z92,z1,z2,z75,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z6,z466])],[(0,[z43,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z467,z6]),(0,[z1,z468,z2,z3,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z8,z194]),(0,[z1,z201,z3,z4,z8,z6,z9]),(0,[z1,z2,z3,z8,z135,z6,z261])],[(0,[z1,z2,z469,z3,z4,z8,z6]),(0,[z1,z470,z2,z3,z4,z8,z6]),(0,[z1,z31,z2,z3,z4,z8,z6])],[(0,[z1,z66,z2,z3,z4,z8,z6]),(0,[z48,z1,z187,z3,z4,z8,z6]),(0,[z471,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z16,z6])],[(0,[z1,z2,z3,z4,z8,z472,z6]),(0,[z1,z212,z98,z3,z4,z8,z6])]],
   [[(0,[z48,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z473]),(0,[z29,z1,z2,z3,z4,z20,z6]),(0,[z1,z72,z2,z3,z155,z8,z6]),(0,[z1,z2,z3,z4,z8,z90,z6])],[(1,[z48,z187,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z80,z8,z16]),(0,[z1,z2,z474,z3,z4,z8,z6])],[],[(0,[z1,z2,z3,z4,z8,z475,z6]),(0,[z1,z2,z3,z476,z4,z8,z6]),(0,[z1,z2,z477,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z68,z9]),(0,[z1,z478,z2,z3,z4,z8,z6]),(0,[z1,z2,z479,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z386]),(0,[z1,z480,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z39,z16]),(0,[z1,z2,z3,z4,z8,z6,z481])],[(0,[z1,z2,z3,z4,z8,z6,z202])],[(0,[z1,z482,z2,z3,z4,z8,z6]),(0,[z142,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z483,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z484])],[]],
   [[(0,[z1,z2,z2,z3,z4,z8,z6]),(0,[z485,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z486,z6]),(0,[z1,z2,z487,z3,z4,z8,z6]),(0,[z488,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z89,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z489]),(0,[z1,z14,z2,z3,z4,z112,z6]),(0,[z1,z490,z2,z3,z4,z8,z6]),(0,[z1,z491,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z492])],[(0,[z1,z493,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z8,z6]),(0,[z1,z243,z2,z3,z4,z8,z6]),(0,[z494,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z495,z3,z4,z8,z6])],[(0,[z1,z2,z19,z3,z4,z8,z6]),(0,[z1,z2,z496,z3,z4,z8,z6]),(0,[z1,z2,z497,z3,z4,z8,z6]),(0,[z1,z2,z3,z290,z4,z8,z135])],[(0,[z48,z1,z2,z3,z4,z8,z386]),(0,[z1,z2,z498,z3,z4,z8,z6]),(0,[z1,z201,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z499,z8,z6]),(0,[z1,z7,z2,z306,z4,z8,z6])],[(0,[z48,z2,z187,z3,z4,z8,z6]),(0,[z1,z500,z2,z3,z4,z8,z6]),(0,[z83,z43,z2,z3,z4,z8,z6]),(0,[z83,z1,z2,z3,z4,z8,z16]),(0,[z1,z501,z2,z3,z4,z8,z6]),(0,[z1,z502,z2,z3,z4,z8,z6]),(0,[z1,z2,z503,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z504,z8,z6])],[(0,[z1,z2,z3,z4,z8,z505,z6]),(0,[z1,z506,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z9,z434]),(0,[z1,z2,z3,z4,z8,z507,z6]),(1,[z1,z31,z2,z3,z25,z6]),(0,[z1,z2,z3,z4,z8,z6,z183])],[(1,[z1,z102,z3,z309,z8,z6]),(0,[z1,z76,z7,z2,z4,z8,z6]),(0,[z508,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z509,z8,z6]),(0,[z510,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z511,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z512]),(0,[z1,z2,z3,z513,z4,z8,z6]),(0,[z1,z2,z3,z4,z514,z8,z6]),(0,[z1,z2,z3,z4,z8,z25,z9]),(0,[z1,z2,z3,z4,z8,z6,z515]),(0,[z1,z2,z516,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z517,z4,z8,z6]),(0,[z1,z518,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z8,z93,z6,z30]),(0,[z1,z2,z3,z4,z519,z8,z6]),(0,[z1,z2,z3,z4,z8,z520,z6])],[(0,[z1,z521,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z522,z4,z8,z6]),(0,[z1,z2,z3,z4,z523,z8,z6])],[(0,[z1,z312,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z524,z8,z6]),(1,[z1,z2,z3,z452,z4,z8]),(0,[z29,z1,z2,z279,z4,z8,z6]),(0,[z1,z2,z3,z4,z525,z8,z6])],[(0,[z526,z1,z2,z3,z4,z8,z6]),(0,[z1,z527,z2,z3,z4,z8,z6])],[(0,[z528,z1,z2,z3,z4,z8,z6]),(0,[z529,z1,z2,z3,z4,z8,z6]),(0,[z1,z46,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z65,z4,z25,z6]),(0,[z1,z2,z3,z530,z4,z8,z6])],[(0,[z1,z2,z3,z143,z8,z6,z261]),(0,[z1,z2,z3,z452,z4,z143,z8]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z1,z2,z3,z4,z8,z531,z6]),(0,[z1,z532,z2,z3,z4,z8,z6]),(0,[z1,z533,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z534,z4,z8,z6]),(0,[z1,z2,z3,z4,z535,z8,z6])],[(0,[z1,z2,z3,z4,z8,z305,z6]),(0,[z1,z2,z3,z4,z8,z6,z536]),(0,[z1,z537,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z44,z4,z8,z16]),(0,[z12,z1,z2,z3,z4,z148,z6]),(0,[z12,z1,z14,z2,z3,z4,z6]),(0,[z1,z538,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z306,z4,z8,z6]),(0,[z1,z76,z31,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z80,z8,z6]),(0,[z1,z2,z3,z4,z539,z8,z6])],[(0,[z48,z1,z66,z3,z4,z8,z6]),(0,[z48,z1,z2,z104,z4,z8,z6]),(0,[z1,z540,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z541])]],
   [[(1,[z1,z187,z3,z4,z8,z9]),(1,[z1,z2,z3,z4,z8,z70]),(0,[z1,z2,z3,z4,z8,z9,z30]),(0,[z1,z542,z2,z3,z4,z8,z6]),(0,[z543,z1,z2,z3,z4,z8,z6]),(0,[z1,z45,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z334,z8,z6]),(0,[z1,z2,z544,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z5,z6,z183]),(0,[z1,z212,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z16,z134]),(0,[z1,z2,z306,z4,z160,z8,z6])],[(0,[z1,z2,z3,z4,z8,z9,z9]),(0,[z1,z2,z75,z3,z4,z8,z9]),(0,[z1,z2,z3,z545,z4,z8,z6]),(0,[z1,z2,z32,z3,z65,z4,z6]),(0,[z1,z2,z3,z4,z546,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z547]),(0,[z1,z2,z3,z4,z8,z548,z6])],[(0,[z1,z465,z2,z3,z4,z8,z6])],[(0,[z29,z1,z2,z3,z4,z304,z6]),(0,[z1,z14,z2,z3,z4,z8,z531]),(0,[z1,z2,z32,z3,z4,z8,z9]),(0,[z1,z2,z3,z549,z4,z8,z6]),(0,[z1,z7,z2,z3,z4,z8,z6]),(0,[z1,z109,z2,z4,z8,z25,z6]),(0,[z1,z2,z3,z550,z4,z8,z6])],[(1,[z1,z2,z318,z4,z8,z6]),(0,[z1,z58,z3,z4,z112,z8,z6]),(0,[z1,z551,z2,z3,z4,z8,z6])],[(0,[z92,z1,z2,z3,z4,z8,z93]),(0,[z1,z31,z2,z3,z8,z25,z6])],[(0,[z1,z2,z3,z4,z143,z8,z16]),(0,[z29,z1,z46,z2,z3,z4,z8]),(0,[z552,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z29,z2,z3,z4,z8,z6,z30]),(0,[z1,z2,z3,z4,z553,z8,z6]),(0,[z1,z2,z3,z4,z8,z554,z6]),(0,[z1,z46,z2,z3,z4,z8,z202]),(0,[z1,z2,z4,z8,z222,z25,z6])],[(0,[z18,z1,z2,z115,z4,z8,z6]),(0,[z2,z19,z3,z115,z4,z8,z6]),(0,[z83,z1,z2,z3,z4,z8,z6]),(0,[z1,z555,z2,z3,z4,z8,z6]),(1,[z1,z212,z98,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z366]),(0,[z1,z2,z3,z4,z8,z16,z556])],[(0,[z1,z2,z3,z4,z557,z8,z6]),(0,[z142,z1,z2,z19,z4,z8,z6]),(0,[z1,z2,z3,z65,z4,z100,z6])],[(0,[z1,z2,z3,z4,z8,z6,z558]),(1,[z1,z109,z2,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z559]),(0,[z1,z2,z3,z560,z4,z8,z6])],[(0,[z1,z2,z3,z561,z4,z8,z6]),(0,[z1,z2,z562,z3,z4,z8,z6]),(0,[z1,z2,z3,z563,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z6,z261]),(0,[z1,z2,z3,z4,z564,z8,z6])],[(0,[z1,z2,z565,z3,z4,z8,z6]),(0,[z1,z566,z2,z3,z4,z8,z6]),(0,[z1,z2,z98,z3,z4,z8,z16])],[(0,[z567,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z568,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z9,z202]),(0,[z1,z2,z75,z3,z4,z8,z202])],[(1,[z18,z2,z19,z4,z8,z6]),(0,[z1,z569,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z100,z8,z16])]],
   [[(0,[z1,z2,z3,z4,z112,z148,z6]),(0,[z1,z2,z570,z3,z4,z8,z6]),(0,[z92,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z571,z6]),(0,[z1,z2,z572,z3,z4,z8,z6])],[(0,[z1,z2,z3,z573,z4,z8,z6]),(0,[z1,z574,z2,z3,z4,z8,z6])],[(0,[z1,z249,z2,z3,z4,z8,z78]),(0,[z1,z575,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z576,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z16])],[(0,[z1,z2,z3,z44,z4,z8,z6]),(0,[z1,z2,z3,z309,z44,z8,z6]),(1,[z1,z385,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z8,z577,z6]),(0,[z1,z2,z578,z3,z4,z8,z6])],[(0,[z12,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z6,z579]),(0,[z1,z2,z580,z3,z4,z8,z6])],[(0,[z1,z2,z75,z19,z4,z8,z6])],[(0,[z1,z2,z3,z581,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z9,z183])],[(0,[z1,z2,z3,z4,z8,z6,z316]),(1,[z1,z2,z3,z4,z8,z428])]],
   [[(0,[z1,z582,z2,z3,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z583,z6])],[(0,[z1,z3,z4,z112,z8,z167,z6]),(0,[z1,z584,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z585,z4,z8,z6]),(0,[z586,z1,z2,z3,z4,z8,z6]),(0,[z1,z179,z2,z3,z4,z8,z16])],[(0,[z1,z587,z2,z3,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z8,z6]),(0,[z1,z2,z588,z3,z4,z8,z6])],[(0,[z181,z1,z187,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z589,z8,z6]),(1,[z1,z2,z3,z4,z8,z225]),(0,[z1,z2,z3,z4,z143,z8,z6])],[(0,[z1,z2,z590,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z185,z6]),(0,[z1,z2,z591,z3,z4,z8,z6]),(0,[z592,z1,z2,z3,z4,z8,z6]),(0,[z181,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z593,z8,z6]),(0,[z1,z2,z125,z3,z4,z8,z16])],[(0,[z594,z1,z2,z3,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z6,z183]),(0,[z1,z2,z77,z3,z4,z8,z9]),(1,[z1,z2,z3,z4,z334,z6]),(0,[z1,z2,z3,z65,z100,z8,z6])]],
   [[(0,[z1,z249,z2,z3,z4,z8,z595]),(0,[z1,z228,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z596,z8,z6]),(0,[z1,z2,z3,z597,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z598,z9]),(0,[z1,z2,z406,z3,z4,z8,z6]),(0,[z1,z2,z3,z563,z4,z8,z6]),(0,[z1,z2,z3,z599,z4,z8,z6])],[(0,[z1,z2,z3,z115,z4,z8,z9]),(0,[z600,z1,z2,z3,z4,z8,z6])],[(0,[z196,z1,z2,z3,z4,z8,z9]),(0,[z29,z92,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z601])],[(0,[z602,z1,z2,z3,z4,z8,z6]),(0,[z1,z76,z2,z3,z4,z90,z6]),(1,[z1,z26,z3,z4,z8,z6])],[(0,[z1,z2,z187,z3,z4,z8,z16]),(0,[z92,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z603,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z264,z8,z9])],[(0,[z1,z2,z3,z604,z4,z8,z6]),(0,[z1,z2,z3,z605,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z606,z6]),(0,[z1,z2,z3,z4,z607,z8,z6]),(0,[z1,z2,z3,z4,z8,z148,z6]),(0,[z1,z2,z3,z4,z8,z608,z6])]],
   [[(0,[z1,z609,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z598]),(0,[z1,z2,z3,z4,z8,z610,z6]),(0,[z1,z2,z3,z4,z8,z611,z6])],[(0,[z1,z2,z3,z4,z8,z612,z6]),(0,[z1,z613,z2,z3,z4,z8,z6]),(0,[z1,z14,z2,z3,z4,z6,z183]),(0,[z1,z58,z2,z3,z4,z112,z6]),(0,[z1,z614,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z615,z8,z6]),(0,[z1,z616,z2,z3,z4,z8,z6])],[(1,[z1,z312,z2,z3,z4,z6]),(0,[z1,z2,z115,z89,z4,z8,z6]),(0,[z1,z2,z617,z3,z4,z8,z6]),(0,[z1,z2,z618,z3,z4,z8,z6]),(0,[z92,z1,z2,z3,z290,z4,z8]),(0,[z1,z3,z4,z8,z10,z130,z6])],[(0,[z1,z2,z98,z115,z4,z8,z6]),(0,[z1,z2,z619,z3,z4,z8,z6])],[(0,[z18,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z304,z6]),(0,[z1,z2,z3,z4,z620,z8,z6]),(0,[z1,z2,z3,z621,z4,z8,z6]),(0,[z1,z622,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z9,z261]),(0,[z1,z2,z3,z65,z4,z8,z16]),(0,[z1,z76,z2,z3,z4,z8,z6]),(0,[z623,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z269,z6]),(0,[z1,z2,z3,z624,z4,z8,z6]),(0,[z1,z2,z3,z625,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z626,z6]),(0,[z627,z1,z2,z3,z4,z8,z6])],[(0,[z1,z628,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z629,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z630]),(1,[z1,z2,z3,z237,z8,z6]),(0,[z1,z2,z3,z4,z631,z8,z6]),(0,[z632,z1,z2,z3,z4,z8,z6]),(0,[z1,z179,z2,z3,z4,z8,z6])]],
   [[(0,[z633,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z634,z4,z8,z6]),(0,[z1,z2,z3,z635,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z636]),(0,[z1,z2,z3,z4,z8,z595,z6]),(0,[z1,z2,z637,z3,z4,z8,z6]),(0,[z1,z638,z2,z3,z4,z8,z6])],[(0,[z1,z2,z639,z3,z4,z8,z6]),(1,[z1,z2,z125,z3,z4,z183])],[(0,[z29,z1,z243,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z73,z6]),(0,[z1,z2,z3,z4,z160,z8,z16])],[(0,[z1,z249,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z155,z8,z6]),(1,[z1,z2,z3,z4,z8,z194]),(0,[z1,z2,z3,z4,z8,z6,z640]),(0,[z1,z2,z32,z4,z160,z8,z6])],[(1,[z1,z2,z3,z4,z8,z78]),(0,[z641,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z642,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z366]),(0,[z643,z1,z2,z3,z4,z8,z6])],[(0,[z181,z1,z66,z3,z4,z8,z6]),(0,[z644,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z290,z4,z8,z16]),(0,[z1,z2,z3,z4,z645,z8,z6]),(0,[z1,z2,z3,z4,z8,z646,z6])],[(0,[z48,z1,z2,z3,z49,z8,z6]),(0,[z1,z2,z3,z4,z647,z8,z6]),(0,[z1,z2,z3,z4,z8,z93,z6]),(0,[z1,z2,z3,z648,z4,z8,z6]),(0,[z1,z2,z3,z4,z649,z8,z6]),(0,[z1,z2,z3,z650,z4,z8,z6])],[(0,[z48,z1,z2,z318,z4,z8,z6]),(0,[z1,z2,z3,z4,z651,z8,z6]),(0,[z1,z2,z3,z652,z4,z8,z6]),(0,[z1,z212,z2,z3,z4,z8,z316]),(1,[z1,z2,z3,z4,z8,z653]),(1,[z1,z2,z3,z4,z6,z21]),(0,[z1,z654,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z655,z6]),(0,[z1,z2,z3,z4,z8,z130,z6])]],
   [[(0,[z1,z656,z2,z3,z4,z8,z6]),(0,[z1,z657,z2,z3,z4,z8,z6]),(0,[z1,z2,z317,z3,z4,z8,z9])],[(0,[z658,z1,z2,z3,z4,z8,z6]),(0,[z321,z1,z2,z3,z4,z8,z9]),(0,[z244,z1,z2,z3,z4,z8,z16]),(0,[z277,z1,z2,z3,z4,z8,z16]),(0,[z1,z76,z2,z3,z306,z8,z6]),(0,[z1,z7,z2,z4,z8,z39,z6]),(0,[z659,z1,z2,z3,z4,z8,z6]),(0,[z660,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z13,z10,z6])],[(0,[z196,z1,z66,z3,z4,z8,z6]),(0,[z142,z1,z2,z3,z4,z8,z9]),(0,[z1,z2,z661,z3,z4,z8,z6]),(0,[z662,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z213]),(0,[z1,z2,z3,z4,z100,z160,z6])],[(0,[z43,z1,z2,z3,z44,z8,z6]),(0,[z1,z2,z3,z4,z8,z663,z6]),(0,[z1,z2,z3,z4,z8,z664,z6]),(0,[z1,z2,z3,z4,z665,z8,z6]),(0,[z1,z76,z2,z3,z4,z168,z6])],[(0,[z1,z2,z3,z4,z666,z8,z6]),(1,[z83,z2,z3,z143,z8,z6]),(0,[z1,z2,z3,z4,z148,z6,z183]),(0,[z1,z2,z3,z4,z8,z6,z74]),(0,[z1,z7,z2,z32,z4,z8,z6])],[(0,[z667,z1,z2,z3,z4,z8,z6]),(0,[z668,z1,z2,z3,z4,z8,z6]),(1,[z1,z465,z2,z3,z4,z8])],[(1,[z1,z2,z3,z133,z8,z6]),(0,[z1,z2,z19,z3,z4,z8,z9]),(0,[z1,z669,z2,z3,z4,z8,z6])],[]],
   [[(0,[z670,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z671,z6]),(1,[z1,z2,z3,z296,z8,z6]),(0,[z1,z2,z3,z4,z672,z8,z6]),(1,[z1,z179,z2,z3,z8,z261])],[(0,[z1,z2,z3,z279,z4,z8,z6]),(0,[z1,z212,z2,z98,z4,z8,z6]),(0,[z1,z2,z3,z4,z673,z8,z6])],[(0,[z18,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z174,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z595]),(0,[z1,z2,z3,z4,z8,z6,z428]),(0,[z1,z2,z3,z4,z8,z674,z6]),(0,[z1,z2,z3,z4,z8,z675,z6]),(0,[z1,z2,z3,z65,z4,z8,z6])],[(0,[z429,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z676,z6])],[(0,[z48,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z3,z677,z4,z8,z6]),(0,[z1,z2,z19,z89,z4,z8,z6]),(0,[z1,z2,z3,z4,z678,z8,z6]),(0,[z1,z2,z3,z4,z8,z679,z6]),(0,[z1,z2,z3,z4,z8,z39,z6]),(0,[z1,z2,z3,z4,z160,z25,z6]),(0,[z1,z2,z3,z4,z8,z680,z6])],[(0,[z1,z2,z3,z681,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z73]),(0,[z1,z2,z3,z4,z8,z438,z6]),(1,[z1,z228,z2,z3,z4,z6]),(0,[z1,z2,z682,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z683])],[(0,[z1,z2,z3,z4,z8,z684,z6]),(0,[z1,z685,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z686,z6]),(0,[z1,z2,z687,z3,z4,z8,z6])],[(1,[z1,z2,z3,z49,z8,z6]),(1,[z1,z2,z3,z4,z20,z6]),(0,[z1,z102,z3,z309,z4,z8,z6]),(0,[z1,z58,z2,z3,z4,z13,z6]),(0,[z287,z1,z2,z3,z4,z8,z16]),(0,[z1,z2,z77,z3,z80,z8,z6]),(0,[z1,z688,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z689,z8,z6]),(0,[z1,z249,z2,z3,z4,z8,z6]),(0,[z1,z102,z2,z3,z4,z8,z653]),(0,[z1,z2,z3,z4,z8,z6,z690]),(0,[z1,z691,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z692,z6]),(1,[z1,z302,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z9]),(0,[z1,z2,z3,z4,z8,z653,z6]),(1,[z1,z2,z3,z4,z8,z531]),(1,[z1,z76,z2,z80,z8,z6]),(0,[z1,z385,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z693,z4,z8,z6]),(0,[z1,z694,z2,z3,z4,z8,z6]),(0,[z1,z2,z695,z3,z4,z8,z6]),(0,[z1,z212,z2,z89,z4,z8,z6]),(0,[z1,z2,z3,z306,z4,z8,z9]),(0,[z1,z2,z3,z290,z4,z8,z6])],[(0,[z1,z2,z3,z309,z4,z8,z9]),(0,[z1,z696,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z697,z8,z6]),(0,[z1,z2,z3,z89,z4,z8,z16]),(0,[z698,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z556,z6])],[(1,[z181,z1,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z699,z6])],[(0,[z277,z1,z2,z3,z4,z8,z6]),(0,[z1,z700,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z309,z143,z8,z6]),(0,[z1,z2,z3,z4,z8,z701,z6]),(0,[z1,z2,z3,z4,z8,z702,z6]),(0,[z1,z7,z2,z3,z65,z4,z6]),(0,[z1,z2,z3,z4,z8,z703,z6]),(0,[z704,z1,z2,z3,z4,z8,z6])],[(0,[z48,z196,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z237,z8,z6]),(0,[z705,z1,z2,z3,z4,z8,z6]),(0,[z1,z706,z2,z3,z4,z8,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z3,z4,z6]),(0,[z1,z201,z3,z4,z8,z708])],[(0,[z1,z3,z4,z311,z8,z9]),(0,[z1,z7,z2,z4,z90,z6]),(0,[z1,z2,z3,z4,z8,z709])],[(0,[z1,z710,z2,z3,z4,z6]),(0,[z1,z313,z3,z4,z8,z9]),(0,[z627,z2,z3,z4,z5,z6]),(0,[z1,z2,z28,z296,z8,z6])],[(0,[z1,z2,z4,z8,z711,z6])],[(0,[z1,z2,z3,z133,z50,z6]),(0,[z1,z302,z2,z4,z8,z202]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z1,z2,z3,z713,z8,z6])],[(0,[z1,z2,z3,z4,z8,z714]),(0,[z1,z2,z3,z4,z8,z715]),(0,[z0,z2,z3,z4,z716,z6]),(0,[z1,z2,z4,z8,z222,z9]),(0,[z1,z7,z2,z4,z39,z16])],[(0,[z1,z2,z3,z4,z717,z6]),(0,[z1,z2,z4,z8,z718,z6])],[(0,[z1,z719,z3,z4,z8,z6]),(0,[z1,z3,z4,z329,z8,z9]),(0,[z1,z3,z4,z269,z8,z9]),(0,[z1,z3,z4,z330,z8,z9])]],
   [[(0,[z187,z3,z4,z8,z598,z9]),(0,[z0,z2,z3,z4,z148,z16]),(0,[z1,z2,z3,z4,z8,z720]),(0,[z1,z574,z3,z4,z8,z9]),(0,[z1,z2,z125,z3,z4,z183])],[(0,[z142,z2,z114,z115,z4,z8]),(0,[z1,z2,z3,z4,z8,z721])],[(0,[z1,z722,z3,z4,z8,z6]),(1,[z1,z2,z723,z8,z6])],[(0,[z1,z2,z3,z133,z247,z6]),(0,[z1,z2,z3,z4,z8,z78]),(0,[z1,z3,z343,z4,z8,z9]),(0,[z1,z706,z3,z4,z8,z9]),(0,[z1,z76,z2,z80,z8,z16])],[(0,[z48,z187,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z168,z6]),(0,[z1,z2,z3,z4,z8,z724])],[(0,[z1,z2,z3,z49,z50,z6]),(0,[z1,z2,z725,z4,z8,z6]),(0,[z1,z174,z3,z4,z8,z6]),(0,[z1,z2,z726,z3,z4,z8]),(0,[z1,z302,z2,z279,z4,z8]),(0,[z1,z2,z3,z4,z8,z727]),(0,[z1,z2,z728,z4,z8,z6]),(0,[z1,z2,z3,z729,z8,z6]),(0,[z1,z3,z4,z8,z16,z101])],[(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z2,z3,z4,z731,z6]),(0,[z2,z3,z732,z4,z8,z6]),(0,[z1,z2,z114,z3,z4,z8]),(0,[z1,z465,z2,z3,z237,z8]),(0,[z1,z2,z3,z4,z6,z21]),(0,[z1,z2,z3,z4,z269,z9]),(0,[z1,z31,z2,z3,z733,z6])],[(0,[z142,z2,z115,z4,z8,z16]),(0,[z1,z734,z3,z4,z8,z6]),(0,[z1,z2,z735,z4,z8,z6]),(0,[z1,z3,z4,z8,z16,z338]),(0,[z1,z736,z3,z4,z8,z6]),(0,[z1,z2,z3,z733,z25,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z185]),(0,[z1,z243,z3,z4,z8,z16]),(0,[z1,z2,z3,z737,z8,z6])],[(0,[z1,z249,z89,z4,z8,z16]),(0,[z1,z317,z3,z4,z112,z9])],[(0,[z1,z2,z3,z4,z8,z738]),(0,[z1,z2,z3,z4,z739,z6]),(0,[z1,z740,z3,z4,z8,z6]),(0,[z1,z2,z741,z4,z8,z6]),(0,[z1,z195,z3,z4,z8,z9])],[(0,[z1,z174,z3,z290,z4,z8])],[(0,[z1,z2,z3,z49,z247,z6]),(0,[z48,z186,z187,z3,z4,z6]),(0,[z1,z421,z3,z4,z8,z9])],[(0,[z1,z2,z318,z4,z247,z6]),(0,[z1,z201,z3,z4,z8,z9]),(0,[z1,z3,z4,z8,z708,z6]),(0,[z1,z76,z2,z499,z8,z6])],[(0,[z1,z742,z3,z4,z8,z6]),(0,[z1,z2,z3,z8,z6,z743]),(0,[z1,z2,z3,z4,z744,z16])],[(0,[z48,z187,z3,z4,z8,z386]),(0,[z1,z2,z3,z8,z745,z6]),(0,[z1,z2,z3,z296,z8,z6]),(0,[z1,z14,z3,z4,z264,z9]),(0,[z1,z2,z746,z4,z8,z6]),(0,[z1,z254,z3,z4,z8,z9]),(0,[z1,z76,z2,z80,z90,z6]),(0,[z1,z179,z2,z3,z8,z261])]],
   [[(0,[z2,z3,z44,z747,z8,z6]),(0,[z1,z184,z3,z4,z8,z9]),(0,[z181,z1,z3,z4,z8,z531]),(0,[z1,z31,z2,z3,z25,z9]),(0,[z1,z67,z2,z3,z8,z261])],[(0,[z1,z2,z3,z4,z8,z595]),(0,[z1,z102,z3,z309,z8,z9]),(1,[z1,z2,z3,z4,z748])],[(0,[z1,z2,z3,z4,z8,z749]),(1,[z2,z3,z747,z8,z6]),(0,[z1,z2,z3,z4,z8,z750]),(0,[z1,z7,z2,z4,z39,z6]),(0,[z1,z2,z3,z100,z733,z6])],[(0,[z1,z2,z3,z4,z8,z751]),(0,[z1,z122,z89,z4,z8,z6]),(0,[z1,z2,z279,z4,z8,z16]),(0,[z1,z58,z3,z4,z752,z6]),(0,[z1,z7,z385,z2,z4,z6])],[(0,[z1,z2,z753,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z754]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z3,z4,z112,z5,z9]),(0,[z1,z755,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z756]),(0,[z0,z2,z3,z4,z148,z6]),(0,[z757,z2,z3,z4,z8,z6]),(0,[z758,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z759,z8,z16]),(0,[z1,z76,z7,z31,z2,z6]),(0,[z1,z2,z3,z4,z8,z760])],[(0,[z1,z26,z3,z4,z13,z10])],[(0,[z1,z2,z3,z4,z761,z6]),(0,[z1,z2,z3,z762,z4,z6]),(0,[z1,z395,z3,z4,z8,z9]),(0,[z1,z2,z75,z4,z8,z676]),(0,[z2,z3,z4,z8,z6,z763]),(0,[z1,z2,z3,z4,z8,z764]),(0,[z1,z58,z3,z4,z112,z366]),(0,[z1,z3,z4,z8,z9,z492]),(0,[z1,z2,z3,z765,z8,z16])]],
   [[(0,[z29,z2,z3,z237,z8,z30]),(0,[z1,z2,z3,z4,z766,z6]),(0,[z1,z76,z2,z80,z8,z6]),(0,[z1,z76,z2,z539,z8,z6]),(0,[z1,z3,z4,z8,z767,z6]),(0,[z1,z2,z75,z4,z8,z134])],[(1,[z768,z3,z4,z8,z6]),(0,[z1,z521,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z769]),(0,[z1,z31,z2,z3,z539,z6]),(0,[z1,z2,z3,z8,z6,z770]),(1,[z1,z109,z31,z2,z6]),(0,[z1,z2,z3,z4,z13,z10])],[(0,[z1,z2,z3,z4,z247,z16]),(0,[z1,z2,z771,z3,z4,z8]),(0,[z1,z2,z772,z3,z4,z8]),(1,[z1,z773,z4,z8,z6]),(0,[z1,z2,z3,z4,z269,z183])],[(0,[z48,z187,z104,z4,z8,z6]),(0,[z48,z768,z3,z4,z8,z6]),(0,[z321,z187,z3,z4,z8,z6]),(0,[z0,z574,z2,z3,z4,z6]),(0,[z526,z1,z3,z4,z8,z16])],[(0,[z1,z2,z732,z4,z8,z6]),(0,[z83,z465,z2,z3,z143,z8]),(0,[z181,z1,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z31,z2,z222,z25,z6])],[(0,[z1,z2,z3,z774,z8,z6]),(0,[z1,z2,z3,z775,z8,z6]),(0,[z1,z2,z28,z4,z304,z6]),(0,[z1,z2,z3,z4,z304,z16]),(0,[z1,z2,z3,z8,z776,z6]),(0,[z1,z15,z2,z4,z8,z131])],[(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z174,z3,z296,z8,z6]),(0,[z1,z249,z89,z4,z8,z6]),(0,[z1,z72,z3,z155,z8,z73]),(0,[z1,z2,z77,z306,z8,z16]),(0,[z1,z2,z406,z4,z8,z134])],[(0,[z1,z2,z3,z4,z8,z778]),(0,[z1,z2,z3,z133,z8,z185]),(0,[z1,z2,z3,z4,z779,z6]),(0,[z83,z2,z3,z747,z8,z6]),(0,[z1,z2,z3,z4,z780,z6]),(0,[z1,z26,z3,z4,z13,z6])]],
   [[(0,[z1,z2,z318,z4,z8,z9]),(0,[z12,z2,z3,z4,z5,z6]),(0,[z1,z58,z3,z4,z112,z16]),(0,[z1,z2,z3,z8,z6,z760])],[(0,[z1,z2,z3,z4,z8,z781]),(0,[z1,z2,z3,z4,z8,z763]),(0,[z1,z782,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z783]),(0,[z1,z3,z425,z4,z8,z9])],[(0,[z1,z186,z187,z3,z4,z9]),(0,[z1,z337,z3,z4,z8,z9]),(0,[z660,z2,z3,z4,z148,z6]),(0,[z1,z2,z3,z4,z744,z6]),(0,[z1,z3,z4,z8,z16,z708])],[(0,[z1,z2,z784,z4,z8,z6]),(0,[z1,z212,z98,z4,z8,z9]),(0,[z1,z76,z2,z723,z8,z6]),(0,[z1,z109,z2,z65,z4,z6])],[(0,[z1,z2,z785,z4,z8,z6]),(0,[z1,z2,z3,z8,z786,z6]),(0,[z1,z2,z3,z787,z8,z6]),(0,[z1,z174,z3,z4,z20,z6]),(0,[z1,z243,z3,z237,z8,z6]),(1,[z1,z2,z3,z733,z6])],[(0,[z1,z2,z3,z4,z8,z788]),(0,[z1,z2,z789,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z790]),(0,[z1,z2,z3,z4,z8,z791]),(0,[z1,z2,z3,z4,z8,z38]),(0,[z1,z109,z2,z4,z8,z9]),(0,[z1,z2,z3,z4,z269,z21]),(0,[z1,z76,z2,z80,z168,z6])],[(0,[z1,z792,z2,z3,z4,z8]),(0,[z1,z793,z2,z3,z8,z6]),(0,[z1,z2,z3,z625,z100,z6]),(0,[z1,z2,z3,z4,z8,z794])]],
   [[(0,[z1,z2,z3,z4,z50,z6]),(0,[z196,z66,z3,z4,z8,z70]),(0,[z1,z2,z279,z4,z8,z6]),(0,[z1,z795,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z796])],[(0,[z18,z2,z19,z4,z8,z9]),(0,[z1,z448,z3,z4,z8,z9]),(0,[z1,z2,z591,z3,z4,z183]),(0,[z1,z2,z3,z759,z8,z6])],[(0,[z1,z2,z318,z4,z8,z386]),(0,[z1,z2,z797,z4,z8,z6]),(0,[z1,z249,z89,z4,z8,z78]),(0,[z1,z3,z4,z752,z8,z6])],[(0,[z1,z2,z3,z765,z8,z6]),(0,[z1,z2,z3,z4,z8,z798]),(0,[z2,z19,z732,z4,z8,z6]),(0,[z29,z2,z3,z4,z8,z556]),(0,[z1,z3,z4,z112,z8,z9]),(0,[z1,z2,z166,z4,z8,z68]),(0,[z1,z46,z2,z4,z8,z17])],[(0,[z66,z768,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z708]),(0,[z1,z109,z2,z4,z39,z6])],[(0,[z1,z72,z3,z155,z8,z16]),(0,[z1,z2,z3,z4,z13,z194]),(0,[z1,z385,z2,z3,z8,z9])],[(0,[z1,z2,z3,z4,z247,z6]),(0,[z2,z3,z4,z5,z716,z6]),(0,[z1,z2,z4,z8,z799,z202])]],
   [[(0,[z1,z2,z3,z800,z8,z6]),(0,[z1,z465,z2,z3,z8,z261]),(0,[z1,z2,z3,z4,z8,z801])],[(0,[z1,z2,z3,z802,z8,z6]),(0,[z1,z2,z3,z4,z8,z803]),(0,[z1,z3,z4,z8,z788,z9]),(0,[z1,z2,z3,z4,z8,z804]),(0,[z244,z2,z3,z4,z8,z93]),(0,[z1,z2,z3,z4,z8,z805])],[(0,[z1,z2,z3,z806,z8,z6]),(0,[z1,z2,z3,z4,z304,z6])],[(0,[z1,z2,z3,z807,z8,z6]),(0,[z1,z2,z77,z306,z8,z6]),(0,[z1,z2,z3,z4,z8,z808])],[(1,[z1,z312,z3,z4,z9]),(0,[z29,z2,z3,z4,z8,z763]),(0,[z1,z2,z3,z4,z8,z809]),(0,[z1,z14,z3,z4,z167,z16]),(0,[z1,z3,z4,z112,z438,z6]),(0,[z1,z2,z4,z723,z8,z6]),(0,[z1,z2,z4,z160,z351,z6]),(0,[z1,z46,z2,z4,z8,z799]),(0,[z1,z109,z31,z2,z8,z6])],[(0,[z1,z2,z3,z4,z810,z16]),(0,[z1,z2,z3,z4,z733,z6])],[(0,[z1,z2,z104,z49,z8,z6]),(0,[z1,z243,z3,z296,z8,z6]),(0,[z1,z682,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z811])],[(0,[z1,z2,z3,z4,z812,z6]),(0,[z2,z768,z3,z4,z8,z6]),(0,[z1,z174,z279,z4,z8,z6])]],
   [[(0,[z1,z3,z4,z8,z16,z9]),(0,[z1,z3,z4,z8,z16,z105])],[(0,[z1,z249,z89,z4,z8,z595]),(0,[z1,z14,z3,z4,z167,z428]),(0,[z1,z2,z3,z4,z16,z813]),(0,[z814,z1,z2,z3,z4,z8])],[(0,[z1,z2,z3,z4,z50,z185]),(0,[z196,z66,z3,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z815]),(0,[z1,z2,z4,z8,z6,z816]),(0,[z1,z2,z3,z4,z334,z9]),(0,[z1,z2,z817,z4,z8,z6])],[(0,[z1,z2,z4,z8,z134,z799])],[(0,[z1,z2,z3,z818,z4,z8]),(0,[z1,z819,z2,z3,z4,z8]),(0,[z1,z76,z228,z2,z3,z6])],[(0,[z1,z276,z98,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z820]),(0,[z1,z2,z821,z4,z8,z6]),(0,[z1,z243,z3,z4,z20,z6]),(0,[z1,z3,z4,z822,z8,z6]),(0,[z1,z14,z3,z4,z8,z9]),(0,[z1,z3,z4,z8,z130,z6])],[(0,[z29,z2,z28,z4,z8,z30]),(0,[z1,z2,z3,z8,z132,z6])],[(0,[z1,z2,z4,z8,z823,z6]),(0,[z1,z26,z3,z4,z8,z9]),(0,[z1,z7,z385,z2,z8,z6])]],
   [[(0,[z1,z2,z3,z824,z8,z6]),(0,[z1,z67,z2,z3,z8,z74]),(0,[z1,z2,z3,z4,z825,z16])],[(0,[z1,z2,z3,z4,z247,z185]),(0,[z1,z174,z3,z4,z304,z6]),(0,[z1,z2,z279,z296,z8,z6]),(0,[z1,z58,z3,z4,z112,z194]),(0,[z1,z2,z3,z4,z826,z9]),(0,[z1,z263,z3,z4,z8,z9]),(0,[z1,z2,z827,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z828]),(0,[z1,z2,z3,z4,z8,z829])],[(0,[z1,z2,z3,z4,z8,z9])],[(0,[z1,z72,z3,z155,z8,z6]),(0,[z1,z830,z2,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z831])],[(0,[z1,z2,z3,z832,z8,z6]),(0,[z1,z2,z104,z4,z8,z16]),(0,[z196,z66,z3,z4,z8,z225]),(0,[z1,z2,z3,z4,z8,z833]),(0,[z1,z496,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z13,z531]),(0,[z1,z2,z834,z3,z4,z6]),(0,[z1,z2,z32,z4,z160,z6]),(0,[z1,z235,z3,z4,z8,z130])],[(0,[z1,z835,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z836]),(0,[z1,z46,z174,z3,z4,z8]),(0,[z1,z2,z3,z4,z16,z837])],[(0,[z1,z312,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z6,z838])],[(0,[z1,z2,z3,z4,z839,z6]),(1,[z2,z3,z4,z716,z6])]],
   [[(0,[z1,z840,z3,z4,z8,z6]),(0,[z1,z2,z279,z4,z20,z6])],[(0,[z1,z2,z3,z4,z8,z841]),(0,[z1,z98,z773,z4,z8,z6]),(0,[z1,z2,z3,z4,z842,z6])],[(0,[z1,z111,z3,z4,z8,z9]),(0,[z1,z2,z3,z237,z8,z9]),(0,[z1,z3,z4,z519,z8,z9]),(0,[z1,z843,z3,z4,z8,z6])],[(0,[z1,z243,z28,z4,z8,z6]),(0,[z1,z2,z3,z296,z304,z6]),(0,[z1,z14,z3,z4,z112,z9]),(0,[z1,z7,z2,z81,z4,z6]),(0,[z1,z7,z2,z119,z4,z6]),(0,[z1,z2,z3,z4,z8,z844]),(0,[z1,z109,z31,z2,z4,z6])],[(0,[z1,z2,z3,z4,z8,z845]),(0,[z69,z2,z3,z44,z8,z6]),(0,[z1,z2,z3,z290,z37,z8]),(1,[z1,z3,z4,z269,z9]),(0,[z1,z2,z3,z846,z8,z6]),(0,[z1,z259,z3,z4,z8,z9])],[(0,[z1,z2,z723,z80,z8,z6])],[],[(0,[z196,z66,z3,z4,z8,z6]),(0,[z1,z186,z2,z3,z4,z16]),(1,[z2,z732,z4,z8,z6]),(0,[z1,z847,z3,z4,z8,z6]),(0,[z1,z848,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z849]),(0,[z1,z102,z3,z309,z8,z653]),(0,[z1,z3,z4,z8,z531,z9])]],
   [[(0,[z1,z3,z4,z8,z305,z9]),(0,[z1,z2,z3,z4,z8,z850]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z852,z4,z8,z6]),(0,[z1,z14,z3,z4,z519,z6]),(0,[z1,z3,z4,z8,z16,z130])],[(0,[z1,z2,z3,z4,z8,z853]),(0,[z1,z854,z3,z4,z8,z6]),(0,[z1,z855,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z856]),(0,[z1,z2,z3,z729,z8,z9]),(0,[z1,z246,z3,z4,z8,z9]),(0,[z1,z2,z3,z857,z4,z6])],[(0,[z768,z187,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z858,z16])],[(0,[z48,z187,z318,z4,z8,z6]),(0,[z1,z2,z3,z859,z8,z6]),(0,[z29,z2,z3,z4,z8,z30]),(0,[z1,z2,z3,z4,z860,z9]),(0,[z321,z2,z3,z4,z8,z434]),(0,[z1,z2,z32,z4,z106,z6])],[(0,[z1,z861,z2,z4,z8,z6]),(0,[z1,z862,z3,z4,z8,z6]),(0,[z1,z863,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z864]),(0,[z1,z2,z865,z4,z8,z16]),(0,[z1,z76,z2,z100,z160,z6]),(0,[z1,z2,z32,z4,z718,z6])],[(0,[z12,z234,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z825,z6]),(0,[z1,z2,z3,z4,z8,z218])],[(0,[z12,z2,z3,z4,z716,z6]),(0,[z1,z2,z827,z4,z8,z6])],[(0,[z83,z2,z3,z143,z8,z9]),(0,[z1,z2,z3,z866,z4,z8]),(0,[z1,z14,z3,z4,z752,z6]),(0,[z1,z2,z3,z4,z16,z21]),(0,[z1,z2,z867,z4,z8,z6])]],
   [[(0,[z1,z465,z2,z3,z290,z8]),(0,[z2,z3,z4,z716,z8,z6]),(0,[z1,z868,z2,z3,z8,z6]),(0,[z1,z2,z77,z8,z373,z6])],[(0,[z1,z2,z104,z4,z8,z6]),(0,[z1,z2,z3,z133,z8,z9]),(0,[z1,z869,z2,z3,z4,z8]),(0,[z1,z389,z3,z4,z112,z6]),(0,[z1,z3,z4,z8,z708,z9]),(0,[z1,z2,z4,z8,z222,z16])],[(0,[z352,z2,z19,z4,z8,z6]),(0,[z1,z2,z870,z4,z8,z6]),(0,[z1,z212,z98,z4,z8,z316])],[(0,[z1,z2,z3,z296,z8,z9]),(0,[z1,z2,z746,z4,z8,z9])],[(0,[z1,z76,z2,z119,z8,z6]),(0,[z1,z46,z2,z4,z8,z202])],[(0,[z1,z2,z3,z871,z8,z6])],[(0,[z1,z3,z4,z872,z8,z6]),(0,[z1,z3,z4,z8,z873,z6]),(0,[z321,z2,z3,z4,z8,z30]),(0,[z1,z2,z874,z4,z8,z6]),(0,[z1,z562,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z264,z438]),(0,[z1,z7,z385,z2,z3,z6])],[(0,[z1,z2,z3,z875,z8,z6]),(0,[z48,z312,z187,z3,z4,z6]),(0,[z1,z273,z3,z4,z8,z9]),(0,[z142,z2,z115,z4,z8,z6]),(0,[z1,z72,z3,z155,z8,z218]),(0,[z1,z2,z3,z8,z16,z743]),(0,[z1,z2,z3,z4,z876,z16])]],
   [[(0,[z1,z243,z3,z4,z8,z6]),(0,[z48,z187,z3,z4,z8,z16]),(0,[z1,z228,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z10,z748])],[(0,[z1,z694,z3,z4,z8,z9])],[(0,[z1,z2,z3,z49,z8,z9]),(0,[z1,z2,z3,z4,z8,z877]),(0,[z1,z3,z4,z112,z148,z9]),(0,[z29,z174,z3,z4,z8,z30]),(0,[z1,z2,z3,z4,z20,z9])],[(0,[z1,z2,z3,z4,z8,z878]),(0,[z1,z2,z879,z4,z8,z6]),(0,[z1,z3,z822,z155,z8,z6])],[(0,[z1,z2,z3,z133,z8,z386]),(0,[z1,z2,z279,z4,z304,z6]),(0,[z1,z2,z3,z4,z8,z880]),(0,[z1,z76,z2,z80,z8,z9]),(0,[z1,z2,z881,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z882])],[(0,[z1,z46,z2,z279,z4,z8]),(0,[z1,z2,z3,z4,z8,z883]),(0,[z1,z45,z2,z3,z8,z124]),(0,[z1,z2,z306,z723,z8,z6])],[(0,[z884,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z885]),(0,[z1,z2,z3,z4,z886,z6])],[(0,[z1,z2,z3,z4,z8,z887]),(0,[z1,z2,z3,z4,z8,z888]),(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z385,z2,z3,z100,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z889]),(0,[z181,z1,z3,z4,z8,z708])],[(0,[z1,z2,z890,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z891]),(0,[z1,z14,z3,z4,z13,z9]),(0,[z1,z58,z3,z4,z6,z492]),(0,[z1,z2,z3,z4,z8,z799])],[(0,[z1,z2,z3,z892,z8,z6]),(0,[z1,z2,z893,z3,z4,z8]),(0,[z1,z584,z3,z4,z8,z16])],[(0,[z1,z14,z3,z4,z167,z531]),(0,[z1,z228,z2,z77,z3,z6]),(0,[z1,z2,z3,z4,z8,z894])],[(0,[z1,z312,z3,z4,z6,z9]),(0,[z12,z2,z3,z4,z5,z9]),(0,[z29,z2,z3,z296,z8,z30]),(0,[z1,z31,z2,z3,z25,z16])],[(0,[z1,z2,z3,z4,z895,z6]),(0,[z1,z2,z3,z49,z8,z386]),(0,[z1,z2,z3,z4,z8,z896]),(0,[z1,z897,z3,z4,z8,z6]),(0,[z1,z2,z898,z4,z8,z6]),(0,[z1,z212,z773,z4,z8,z6]),(0,[z1,z102,z3,z309,z8,z16])],[(0,[z1,z899,z2,z4,z8,z6]),(1,[z1,z76,z228,z2,z6]),(0,[z1,z2,z4,z8,z222,z6]),(0,[z1,z2,z3,z4,z8,z900])],[(0,[z1,z2,z3,z4,z901,z6]),(0,[z1,z3,z309,z822,z8,z6]),(0,[z1,z14,z3,z4,z8,z902]),(0,[z1,z235,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z903])]],
   [[(0,[z1,z2,z104,z133,z8,z6]),(0,[z1,z2,z3,z4,z904,z6]),(0,[z1,z2,z28,z4,z8,z9]),(0,[z1,z905,z2,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z906])],[(0,[z1,z907,z3,z4,z8,z6]),(0,[z1,z2,z3,z8,z786,z9]),(0,[z1,z2,z3,z4,z8,z908])],[(0,[z1,z2,z3,z4,z909,z8]),(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z2,z3,z4,z911,z9])],[(0,[z1,z2,z3,z4,z8,z912]),(0,[z29,z2,z3,z4,z20,z30]),(1,[z1,z3,z4,z8,z708]),(0,[z1,z2,z3,z4,z8,z913]),(0,[z1,z914,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z50,z9]),(0,[z1,z2,z3,z4,z915,z6]),(0,[z1,z2,z3,z4,z876,z6]),(0,[z1,z2,z3,z4,z8,z902]),(0,[z1,z109,z2,z100,z8,z6])],[(0,[z48,z187,z3,z4,z8,z6]),(0,[z1,z14,z3,z4,z158,z6])],[(0,[z1,z2,z3,z4,z916,z6]),(0,[z1,z2,z3,z4,z917,z6]),(0,[z1,z2,z3,z918,z8,z6]),(0,[z1,z312,z187,z3,z4,z9]),(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z2,z3,z920,z8,z6]),(0,[z1,z2,z921,z3,z4,z6]),(0,[z1,z34,z3,z4,z8,z16]),(0,[z1,z2,z3,z723,z8,z6]),(0,[z1,z2,z922,z4,z8,z6])],[(0,[z1,z341,z3,z4,z8,z9])]],
   [[(0,[z632,z2,z3,z44,z8,z6]),(0,[z1,z2,z3,z4,z8,z316]),(0,[z1,z58,z3,z4,z112,z6])],[(0,[z1,z2,z881,z4,z8,z6]),(0,[z227,z2,z3,z4,z148,z6])],[(0,[z1,z2,z3,z4,z269,z262])],[(0,[z142,z2,z732,z4,z8,z6])],[(0,[z1,z2,z318,z4,z8,z16]),(0,[z1,z2,z3,z923,z8,z6]),(0,[z1,z2,z924,z4,z8,z6]),(0,[z1,z2,z4,z925,z8,z6]),(0,[z1,z3,z4,z615,z8,z9]),(0,[z1,z174,z3,z4,z8,z305]),(0,[z92,z2,z3,z4,z8,z763]),(0,[z1,z2,z3,z4,z90,z9]),(0,[z1,z3,z4,z8,z9,z271])],[(0,[z1,z2,z3,z4,z13,z467]),(0,[z1,z618,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z926,z16])],[(0,[z1,z555,z3,z155,z8,z6]),(0,[z1,z609,z3,z4,z8,z9]),(0,[z1,z385,z2,z160,z8,z6])],[(0,[z1,z2,z3,z4,z50,z386]),(0,[z1,z3,z4,z112,z8,z366])]],
   [[(0,[z1,z2,z3,z927,z8,z6]),(0,[z1,z2,z3,z65,z100,z9]),(0,[z1,z2,z3,z4,z928,z6])],[(0,[z1,z2,z3,z4,z8,z929]),(0,[z1,z31,z2,z3,z25,z6])],[(0,[z1,z2,z930,z4,z8,z6]),(0,[z1,z931,z3,z4,z8,z6]),(0,[z1,z102,z3,z309,z8,z6]),(0,[z1,z2,z317,z3,z4,z258])],[(0,[z1,z2,z3,z4,z8,z932]),(0,[z1,z2,z3,z933,z8,z6]),(0,[z1,z11,z3,z4,z8,z9])],[(0,[z552,z2,z115,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z934])],[(0,[z1,z935,z3,z4,z8,z6]),(0,[z29,z2,z279,z4,z8,z30]),(0,[z1,z76,z2,z334,z80,z6]),(0,[z1,z936,z3,z4,z8,z6])],[(0,[z18,z2,z19,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z937]),(0,[z1,z2,z3,z452,z4,z8])],[(0,[z1,z2,z3,z938,z4,z8]),(0,[z1,z2,z707,z3,z4,z9])]],
   [[(0,[z1,z2,z3,z4,z939,z6]),(0,[z1,z3,z4,z647,z8,z9]),(0,[z1,z2,z3,z4,z8,z940]),(0,[z1,z170,z3,z4,z8,z16]),(0,[z1,z76,z228,z2,z80,z6]),(0,[z1,z2,z306,z8,z136,z6]),(0,[z1,z2,z4,z8,z6,z941]),(0,[z1,z2,z3,z8,z760,z261])],[(0,[z1,z2,z3,z4,z8,z942]),(0,[z1,z3,z4,z8,z943,z6]),(0,[z1,z3,z4,z112,z752,z6]),(0,[z1,z3,z4,z8,z130,z9]),(0,[z1,z3,z4,z8,z655,z9])],[(0,[z1,z944,z3,z4,z8,z6]),(0,[z1,z72,z3,z822,z8,z6]),(0,[z1,z2,z4,z8,z711,z9]),(0,[z1,z2,z3,z8,z132,z9]),(0,[z1,z385,z2,z3,z8,z16])],[(0,[z1,z2,z3,z4,z8,z945]),(0,[z1,z2,z104,z4,z50,z6])],[(0,[z1,z2,z3,z4,z8,z70]),(0,[z48,z187,z3,z133,z8,z6]),(0,[z1,z2,z3,z946,z4,z6]),(0,[z1,z2,z3,z4,z8,z947]),(0,[z1,z2,z3,z4,z8,z948]),(0,[z1,z14,z3,z4,z167,z6])],[(0,[z92,z2,z3,z599,z4,z8]),(0,[z1,z2,z3,z4,z810,z6]),(0,[z1,z638,z3,z4,z8,z9])],[(0,[z1,z2,z3,z4,z8,z949]),(0,[z2,z3,z4,z716,z148,z6]),(0,[z1,z2,z3,z4,z13,z21])],[(0,[z0,z1,z14,z3,z4,z9]),(0,[z29,z2,z3,z4,z304,z30]),(0,[z1,z72,z3,z155,z8,z9]),(0,[z1,z2,z3,z4,z6,z950])]],
   [[(0,[z1,z2,z3,z4,z8,z386]),(0,[z1,z413,z3,z4,z8,z9]),(0,[z1,z2,z3,z951,z8,z6]),(0,[z1,z2,z4,z8,z952,z6]),(0,[z1,z14,z3,z4,z8,z366]),(0,[z1,z2,z32,z4,z160,z9]),(0,[z1,z2,z3,z4,z8,z748])],[(0,[z543,z66,z3,z4,z8,z6])],[(0,[z1,z2,z104,z4,z247,z6]),(0,[z404,z2,z3,z143,z8,z6]),(0,[z1,z174,z3,z4,z8,z30]),(0,[z1,z243,z279,z4,z8,z6]),(0,[z181,z1,z3,z4,z16,z21]),(0,[z1,z7,z385,z2,z39,z6]),(0,[z1,z953,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z954]),(0,[z1,z2,z3,z4,z168,z9]),(0,[z1,z3,z4,z673,z8,z9])],[(0,[z1,z174,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z955]),(0,[z1,z2,z3,z956,z8,z6]),(0,[z1,z2,z3,z4,z8,z957]),(0,[z1,z2,z3,z958,z4,z8]),(0,[z1,z14,z3,z4,z6,z258])],[(0,[z48,z187,z3,z49,z8,z6]),(0,[z1,z2,z3,z4,z8,z366]),(0,[z1,z2,z3,z4,z959,z16])],[(0,[z1,z2,z3,z960,z8,z6]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z2,z3,z4,z962,z6]),(0,[z83,z2,z3,z452,z143,z8]),(0,[z1,z2,z3,z4,z8,z963]),(0,[z1,z2,z3,z4,z334,z16]),(0,[z1,z109,z31,z2,z3,z6])],[(0,[z2,z732,z115,z4,z8,z6]),(1,[z2,z3,z4,z8,z763]),(0,[z1,z2,z3,z4,z16,z838]),(0,[z1,z2,z4,z160,z718,z6])]],
   [[(0,[z1,z2,z3,z237,z20,z6]),(0,[z1,z2,z3,z846,z8,z9])],[(0,[z1,z2,z3,z4,z8,z964]),(0,[z1,z2,z3,z4,z8,z965]),(0,[z1,z2,z966,z4,z8,z6]),(0,[z1,z2,z3,z4,z269,z531]),(0,[z1,z2,z3,z4,z8,z967])],[(0,[z1,z2,z968,z4,z8,z6]),(0,[z1,z2,z75,z4,z8,z68]),(0,[z1,z385,z2,z32,z3,z6])],[(0,[z1,z969,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z970]),(0,[z1,z15,z2,z4,z8,z202]),(0,[z1,z26,z3,z4,z8,z16])],[(0,[z1,z2,z971,z4,z8,z6]),(0,[z1,z2,z3,z4,z972,z6]),(0,[z1,z973,z2,z3,z8,z6]),(0,[z704,z2,z3,z143,z8,z6]),(0,[z1,z243,z3,z4,z304,z6]),(0,[z974,z2,z3,z4,z8,z6]),(0,[z1,z385,z2,z3,z25,z6]),(0,[z1,z2,z3,z65,z417,z6]),(0,[z1,z2,z3,z8,z733,z6])],[(0,[z1,z125,z3,z4,z8,z130])],[(0,[z1,z3,z4,z8,z556,z9])],[(0,[z1,z2,z3,z4,z8,z975]),(0,[z1,z976,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z1,z495,z3,z4,z8,z16])]],
   [[(0,[z1,z2,z3,z4,z8,z977])],[(0,[z1,z2,z3,z4,z978,z6]),(0,[z1,z2,z75,z279,z4,z8]),(0,[z1,z2,z3,z4,z8,z979]),(0,[z1,z14,z3,z4,z514,z6]),(0,[z1,z7,z2,z4,z39,z9])],[(0,[z1,z312,z2,z3,z4,z16])],[(0,[z1,z2,z3,z980,z8,z6]),(0,[z1,z2,z3,z4,z8,z981]),(0,[z1,z2,z3,z822,z8,z6]),(0,[z1,z2,z3,z4,z8,z428]),(0,[z1,z2,z867,z4,z8,z9]),(0,[z1,z3,z4,z269,z6,z9]),(0,[z1,z3,z4,z13,z10,z130])],[(0,[z1,z2,z3,z4,z8,z982]),(0,[z1,z983,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z148,z9]),(0,[z1,z984,z3,z4,z8,z6])],[(0,[z1,z2,z985,z4,z8,z6]),(0,[z18,z2,z732,z4,z8,z6]),(0,[z1,z3,z4,z8,z23,z9]),(0,[z986,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z531,z183]),(0,[z1,z2,z3,z4,z269,z16])],[(0,[z1,z2,z3,z4,z8,z987]),(0,[z1,z988,z2,z3,z4,z8]),(0,[z1,z2,z28,z237,z8,z6]),(0,[z1,z2,z3,z237,z8,z16]),(0,[z1,z2,z3,z4,z8,z989])],[(0,[z48,z187,z3,z4,z50,z6]),(0,[z1,z186,z2,z3,z4,z6]),(0,[z1,z302,z2,z75,z4,z8]),(0,[z1,z990,z2,z3,z4,z6]),(0,[z1,z2,z77,z723,z8,z6]),(0,[z1,z2,z3,z991,z4,z6]),(0,[z1,z2,z3,z4,z8,z992])]],
   [[(0,[z1,z2,z318,z133,z8,z6]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z92,z2,z215,z3,z4,z8]),(0,[z1,z212,z98,z4,z8,z213]),(0,[z1,z994,z3,z4,z8,z6]),(1,[z1,z2,z4,z718,z6])],[],[(0,[z1,z2,z3,z4,z8,z995]),(0,[z321,z187,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z959,z6]),(0,[z2,z3,z747,z143,z8,z6]),(0,[z1,z249,z773,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z996]),(0,[z142,z2,z115,z4,z8,z9]),(0,[z1,z3,z4,z8,z54,z9]),(0,[z1,z2,z4,z160,z90,z6]),(0,[z1,z2,z3,z4,z334,z6]),(0,[z1,z2,z3,z65,z733,z6])],[(0,[z1,z2,z865,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z997]),(0,[z1,z243,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z998]),(0,[z1,z2,z3,z999,z8,z6])],[(0,[z1,z2,z1000,z3,z4,z8]),(0,[z1,z2,z1001,z4,z8,z6]),(0,[z1,z249,z89,z4,z8,z9]),(0,[z1,z300,z3,z4,z8,z16]),(0,[z1,z109,z2,z4,z160,z6])],[(0,[z1,z2,z104,z4,z8,z185]),(0,[z1,z2,z3,z4,z731,z16])],[(0,[z1,z2,z3,z4,z1002,z6]),(0,[z1,z3,z4,z8,z70,z9]),(0,[z1,z2,z3,z4,z8,z1003])]],
   [[(0,[z1,z2,z1004,z3,z4,z6]),(0,[z1,z1005,z2,z3,z4,z8]),(0,[z1,z1006,z2,z3,z4,z6]),(0,[z1,z3,z773,z4,z8,z6]),(0,[z1,z26,z3,z4,z8,z6]),(0,[z1,z1007,z2,z4,z8,z6])],[(0,[z1,z2,z318,z49,z8,z6]),(0,[z1,z2,z3,z4,z269,z10])],[(0,[z1,z2,z3,z4,z826,z6]),(0,[z1,z102,z3,z309,z8,z38]),(0,[z1,z2,z3,z8,z6,z1008])],[(0,[z83,z2,z3,z143,z8,z16]),(0,[z1,z2,z3,z4,z8,z1009]),(0,[z1,z2,z75,z4,z8,z799]),(0,[z1,z2,z3,z4,z748,z183])],[(0,[z1,z3,z4,z8,z1010,z6]),(0,[z1,z2,z1011,z4,z8,z6]),(0,[z1,z3,z4,z16,z9,z21])],[(0,[z1,z2,z3,z133,z8,z16]),(0,[z1,z2,z3,z4,z8,z1012]),(0,[z1,z14,z3,z4,z9,z258]),(0,[z1,z96,z3,z4,z8,z9])],[(0,[z1,z685,z3,z4,z8,z9])],[(0,[z1,z312,z2,z3,z4,z6]),(0,[z1,z2,z279,z4,z8,z9]),(0,[z1,z2,z3,z296,z8,z16]),(0,[z1,z179,z2,z3,z8,z760])]],
   [[(0,[z1,z2,z3,z4,z1013,z6]),(0,[z1,z2,z3,z4,z1014,z6]),(0,[z1,z2,z3,z4,z8,z1015]),(0,[z1,z179,z174,z3,z4,z8]),(0,[z2,z3,z4,z8,z93,z763]),(0,[z1,z2,z3,z4,z13,z438]),(0,[z1,z2,z3,z4,z8,z1016])],[(0,[z1,z462,z3,z4,z8,z16])],[(0,[z1,z2,z3,z4,z70,z1017]),(0,[z1,z2,z3,z4,z269,z6])],[(0,[z1,z2,z1018,z3,z4,z8]),(0,[z1,z2,z3,z237,z8,z6])],[(0,[z1,z2,z3,z4,z1019,z70]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1,z2,z3,z1021,z8,z6]),(0,[z1,z342,z3,z4,z8,z9]),(0,[z1,z228,z2,z3,z4,z16]),(0,[z1,z228,z2,z306,z4,z6]),(0,[z1,z2,z3,z4,z13,z748])],[(0,[z1,z58,z496,z3,z4,z6]),(0,[z29,z243,z3,z4,z8,z30]),(0,[z1,z2,z3,z1022,z8,z6])],[(0,[z1,z2,z3,z49,z8,z16]),(0,[z1,z2,z3,z4,z247,z9]),(0,[z1,z2,z28,z4,z20,z6]),(0,[z1,z2,z3,z4,z20,z16]),(0,[z1,z31,z2,z3,z90,z6])],[(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z4,z8,z194]),(0,[z1,z2,z4,z8,z6,z1024]),(0,[z1,z3,z4,z8,z1025,z6])]],
   [[(0,[z1,z2,z3,z1026,z4,z8]),(0,[z1,z2,z3,z4,z1027,z6])],[(0,[z1,z2,z1028,z3,z4,z8]),(0,[z1,z2,z3,z4,z304,z9]),(0,[z1,z379,z2,z4,z8,z17]),(0,[z1,z31,z2,z283,z3,z6])],[(0,[z1,z685,z3,z4,z167,z6]),(0,[z1,z2,z77,z306,z8,z9])],[(0,[z1,z2,z318,z4,z50,z6]),(0,[z641,z2,z19,z4,z8,z6]),(0,[z1,z174,z75,z3,z4,z8]),(0,[z1,z212,z98,z4,z8,z16]),(0,[z1,z2,z3,z4,z8,z653]),(0,[z1,z2,z3,z4,z8,z1029]),(0,[z1,z3,z4,z141,z8,z9]),(0,[z1,z3,z4,z112,z438,z9])],[(0,[z1,z2,z1030,z3,z4,z8]),(0,[z1,z58,z3,z4,z112,z9]),(0,[z1,z2,z3,z4,z860,z6])],[(0,[z1,z109,z2,z4,z8,z16]),(0,[z1,z2,z4,z718,z39,z6])],[(0,[z339,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z8,z763,z30]),(0,[z1,z2,z3,z4,z8,z213]),(0,[z1,z3,z4,z752,z167,z6])],[(0,[z181,z1,z3,z4,z8,z70]),(0,[z1,z2,z3,z4,z1031,z6]),(0,[z1,z214,z3,z4,z8,z9]),(0,[z244,z2,z3,z4,z8,z305]),(0,[z1032,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z312,z3,z4,z8,z9]),(0,[z83,z2,z3,z143,z8,z6]),(0,[z12,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z8,z1033]),(0,[z1,z2,z1034,z4,z8,z6])],[(0,[z1,z2,z3,z4,z247,z386]),(0,[z1,z2,z3,z4,z1035,z6]),(0,[z1,z465,z2,z3,z4,z8]),(0,[z1,z2,z125,z3,z4,z21])],[(0,[z1,z2,z3,z133,z8,z6]),(0,[z48,z187,z3,z4,z8,z185]),(0,[z2,z3,z4,z747,z8,z6]),(0,[z43,z2,z3,z747,z8,z6]),(0,[z1,z14,z184,z3,z4,z6]),(0,[z1,z174,z3,z237,z8,z6]),(0,[z1,z235,z2,z3,z4,z21]),(0,[z1,z2,z3,z100,z90,z6])],[(0,[z1,z2,z3,z4,z1036,z6]),(0,[z508,z2,z115,z4,z8,z6])],[(0,[z1,z66,z3,z4,z8,z788]),(0,[z1,z3,z4,z178,z8,z9]),(0,[z1,z2,z28,z4,z8,z16])],[(0,[z1,z2,z3,z4,z8,z1037]),(0,[z1,z2,z3,z4,z1038,z6])],[(0,[z1,z2,z1039,z3,z4,z8]),(0,[z1,z2,z4,z8,z16,z816])],[(0,[z1,z187,z3,z4,z8,z9]),(0,[z1,z457,z3,z4,z8,z16])]],
   [[(0,[z1,z2,z3,z4,z50,z16]),(0,[z1,z1040,z2,z3,z8,z6]),(0,[z142,z302,z2,z115,z4,z8])],[(0,[z1,z1041,z3,z4,z8,z6]),(0,[z1,z2,z3,z1042,z8,z6]),(0,[z1,z538,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z73]),(0,[z1,z109,z2,z4,z90,z6]),(0,[z1,z228,z2,z3,z4,z6])],[(0,[z1,z1043,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z1,z26,z3,z4,z8,z531])],[(0,[z1,z2,z3,z49,z8,z6]),(0,[z1,z2,z1045,z4,z8,z6]),(0,[z66,z187,z3,z4,z8,z9]),(0,[z1,z1046,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z8,z1047]),(0,[z1,z3,z4,z8,z902,z9]),(0,[z1,z14,z3,z4,z9,z183]),(0,[z1,z2,z3,z4,z8,z1048]),(0,[z1,z3,z4,z13,z8,z130])],[(0,[z1,z2,z318,z4,z8,z6]),(0,[z1,z2,z3,z1049,z8,z6]),(0,[z1,z2,z773,z4,z8,z6])],[(0,[z1,z2,z3,z4,z926,z6]),(0,[z1,z2,z3,z1050,z8,z6]),(0,[z1,z302,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z1,z2,z3,z4,z8,z531])],[(0,[z1,z2,z3,z4,z8,z1052])],[(0,[z1,z2,z3,z4,z8,z1053])]],
   [[(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z212,z98,z4,z8,z6]),(0,[z1,z14,z3,z4,z167,z9]),(0,[z1,z2,z3,z4,z90,z16])],[(0,[z1,z2,z3,z4,z1055,z8]),(0,[z429,z2,z3,z4,z8,z598]),(0,[z1,z2,z3,z802,z8,z16]),(0,[z1,z385,z2,z3,z90,z6])],[(0,[z1,z2,z1056,z4,z8,z6]),(0,[z1,z187,z3,z4,z8,z386]),(0,[z1,z1057,z2,z3,z4,z8]),(0,[z1,z109,z2,z4,z8,z6]),(0,[z1,z76,z228,z2,z8,z6])],[(0,[z29,z491,z2,z3,z4,z8]),(0,[z1,z1058,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z1059,z6])],[(0,[z196,z768,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1060]),(0,[z1,z2,z3,z65,z100,z16]),(0,[z1,z179,z2,z3,z8,z124])],[(0,[z181,z1,z312,z3,z4,z6]),(0,[z1,z700,z3,z4,z8,z9]),(0,[z1,z2,z75,z88,z4,z8]),(0,[z1,z616,z3,z4,z8,z9]),(0,[z1,z2,z3,z4,z8,z1061])],[(0,[z196,z66,z3,z4,z8,z9]),(0,[z18,z2,z19,z4,z8,z6]),(0,[z1,z3,z4,z8,z1062,z6])],[(0,[z1,z2,z3,z1063,z8,z6]),(0,[z1,z2,z3,z747,z8,z6])]],
   [[(0,[z1,z2,z3,z1064,z8,z6]),(0,[z181,z1,z3,z4,z269,z16])],[(0,[z1,z2,z3,z4,z8,z16]),(0,[z1,z905,z2,z4,z8,z6]),(0,[z1,z2,z28,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1065]),(0,[z1,z2,z3,z4,z8,z1066]),(0,[z1,z385,z2,z3,z8,z6])],[(0,[z1,z2,z3,z4,z1019,z6]),(0,[z1,z2,z3,z4,z194,z183]),(0,[z1,z2,z3,z4,z911,z6]),(0,[z1,z2,z317,z3,z4,z183])],[(0,[z1,z1067,z2,z3,z4,z8]),(0,[z1,z537,z3,z309,z8,z6]),(0,[z92,z2,z3,z4,z8,z598]),(0,[z1068,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z9,z21])],[(0,[z1,z2,z3,z49,z8,z185]),(0,[z1,z179,z2,z3,z237,z8]),(0,[z1069,z2,z3,z4,z8,z6]),(1,[z1,z3,z4,z752,z6]),(0,[z1,z478,z3,z4,z8,z9]),(0,[z1,z7,z2,z4,z718,z6])],[(0,[z1,z2,z318,z4,z8,z185]),(0,[z1,z768,z3,z4,z8,z6]),(0,[z1,z174,z3,z4,z8,z93]),(0,[z1,z2,z3,z8,z132,z16])],[(0,[z1,z2,z3,z4,z1070,z6]),(0,[z1,z3,z4,z8,z1071,z6]),(0,[z1,z260,z3,z4,z8,z9]),(0,[z29,z401,z2,z3,z4,z8]),(0,[z1,z773,z89,z4,z8,z6]),(0,[z1,z1072,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1073])]],
   [[(0,[z1,z66,z3,z4,z8,z9]),(0,[z1,z2,z104,z4,z8,z9]),(0,[z1,z2,z3,z1074,z4,z8]),(0,[z12,z1,z14,z3,z4,z9]),(0,[z1,z2,z3,z4,z6,z813]),(0,[z1,z102,z3,z822,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1075]),(1,[z1,z3,z822,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1076]),(0,[z1,z2,z3,z1077,z8,z6]),(0,[z287,z2,z3,z4,z8,z556]),(0,[z1,z2,z3,z4,z8,z1078])],[(0,[z1,z2,z3,z4,z8,z225]),(0,[z1,z2,z3,z4,z8,z1079]),(0,[z1,z2,z1080,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1081]),(0,[z1,z2,z1082,z4,z8,z6]),(0,[z1,z2,z3,z296,z20,z6]),(0,[z1,z3,z4,z8,z278,z9]),(0,[z1,z2,z32,z4,z160,z16]),(0,[z1,z2,z3,z100,z699,z6])],[(0,[z1,z1083,z3,z4,z8,z6]),(0,[z1,z2,z279,z237,z8,z6]),(0,[z1,z2,z3,z4,z90,z6]),(0,[z1,z2,z450,z4,z160,z6])],[(0,[z1,z2,z406,z4,z8,z396]),(0,[z1,z109,z31,z2,z25,z6])],[(0,[z1,z2,z3,z4,z8,z1084]),(0,[z92,z2,z3,z4,z8,z93]),(0,[z1,z2,z3,z4,z194,z21]),(0,[z1,z2,z3,z4,z168,z16]),(0,[z1,z7,z2,z132,z39,z6]),(0,[z1,z2,z4,z8,z6,z799])]],
   [[(0,[z1,z2,z1085,z4,z8,z6]),(0,[z1,z174,z28,z4,z8,z6]),(0,[z1,z174,z3,z4,z8,z16]),(0,[z1,z983,z2,z3,z8,z9])],[(0,[z48,z187,z3,z4,z247,z6]),(0,[z1,z2,z3,z4,z8,z1086]),(0,[z1,z2,z3,z4,z842,z16]),(0,[z1,z76,z228,z2,z4,z6]),(0,[z1,z2,z3,z65,z100,z6]),(0,[z1,z2,z3,z4,z6,z748])],[(0,[z1,z2,z3,z4,z8,z1087]),(0,[z1,z2,z3,z4,z6,z1017]),(0,[z1,z470,z3,z4,z8,z9]),(0,[z1,z3,z4,z8,z9,z414])],[(0,[z1,z66,z3,z4,z8,z386]),(0,[z1,z2,z104,z4,z8,z386]),(0,[z1,z186,z2,z3,z4,z9]),(0,[z1,z1088,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1089]),(0,[z1,z2,z3,z4,z8,z1090]),(0,[z1,z2,z3,z4,z8,z1091])],[(0,[z1,z2,z3,z4,z8,z1092]),(0,[z1,z2,z3,z4,z6,z837]),(0,[z1,z3,z4,z269,z16,z9]),(0,[z1,z2,z3,z4,z6,z1093]),(1,[z1,z7,z385,z2,z6])],[(0,[z43,z2,z3,z44,z8,z6]),(0,[z181,z1,z3,z4,z269,z6]),(1,[z1,z2,z4,z8,z799])],[(0,[z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z1094,z4,z8,z6]),(0,[z1,z243,z3,z4,z8,z70]),(0,[z1,z2,z3,z290,z237,z8])],[(0,[z1,z2,z3,z237,z304,z6]),(0,[z1,z1095,z3,z4,z8,z6]),(0,[z1,z2,z125,z3,z4,z748]),(0,[z1,z26,z3,z4,z6,z183])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 532) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 532).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1065).take 112) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1177)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [532, 533, 112] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 131).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 248).take 8).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 131, 8] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_43472

theorem PEqualNP.Outside.L_meta_43472 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272482944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272482944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43472.solve