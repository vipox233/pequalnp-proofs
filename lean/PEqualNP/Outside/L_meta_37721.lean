import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37721

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1000081040c51450#64 ++ 0x21000081040c5145#64 ++ 0xec051a33c3cf3cff#64 ++ 0xfec051a33c3cf3cf#64 : BitVec 256),
   (0xa00860c522124921#64 ++ 0x8a00860c52212492#64 ++ 0xde1ae5cd2233cf3d#64 ++ 0xfde1ae5cd2233cf3#64 : BitVec 256),
   (0x0063060a0c28a284#64 ++ 0x40063060a0c28a28#64 ++ 0xbde3060e3c3cf3cf#64 ++ 0xabde3060e3c3cf3c#64 : BitVec 256),
   (0xc1bc07703740fc06#64 ++ 0x8c1bc07703740fc0#64 ++ 0x79fc07f03fc0fc0b#64 ++ 0x679fc07f03fc0fc0#64 : BitVec 256),
   (0x02dfb8003bbf0008#64 ++ 0xf02dfb8003bbf000#64 ++ 0xfbfff8003fff0007#64 ++ 0x1fbfff8003fff000#64 : BitVec 256),
   (0x00f7d7af8000000f#64 ++ 0x000f7d7af8000000#64 ++ 0xfaffffffc0000000#64 ++ 0xffaffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde3060e3c3cf3cf 0xabde3060e3c3cf3c

def z1 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc0000000 0xffaffffffc000000

def z2 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8003fff0007 0x1fbfff8003fff000

def z3 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x0000000003c30c30 0x00000000003c30c3

def z4 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xec051a33c3cf3cff 0xfec051a33c3cf3cf

def z5 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1ae5cd2233cf3d 0xfde1ae5cd2233cf3

def z6 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f03fc0fc0b 0x679fc07f03fc0fc0

def z7 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xa5e3020e1c3c33c6 0x8a5e3020e1c3c33c

def z8 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x21e402301dc03002 0x021e402301dc0300

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0xec051a33c00c30cf 0xfec051a33c00c30c

def z10 : W := mkw 0x009491208000000a 0x0009491208000000 0x00041830c0000000 0x000041830c000000

def z11 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x421cf9f1c0000000 0x5421cf9f1c000000

def z12 : W := mkw 0x1000080040850050 0x2100008004085005 0x00001801c0030030 0x100001801c003003

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c02040c2030c30d 0xa9c02040c2030c30

def z14 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfe07fc3ff0ff0f 0xefdfe07fc3ff0ff0

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000002030c3d 0x00400000002030c3

def z16 : W := mkw 0xe1fff7ffb752fd2f 0x8e1fff7ffb752fd2 0xfffffffffff3ff3f 0xffffffffffff3ff3

def z17 : W := mkw 0x1000001040401450 0x0100000104040145 0x04000233c0003cf8 0xe04000233c0003cf

def z18 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0x13fae0003c300000 0x013fae0003c30000

def z19 : W := mkw 0x1000001040401450 0x0100000104040145 0x00000232c00030c0 0x000000232c00030c

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0xac010202000c30cf 0xaac010202000c30c

def z21 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfd07f23fccfccf 0xefdfd07f23fccfcc

def z22 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffe030c30d 0xffeffffffe030c30

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00000102030c3d 0xfcc00000102030c3

def z24 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8013fff0c3f 0xffffff8013fff0c3

def z25 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0x421cf80003c30000 0x1421cf80003c3000

def z26 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x12fae5cc00000000 0x012fae5cc0000000

def z27 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x11e2040c3c30c300 0x011e2040c3c30c30

def z28 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfffffffffc3cf3cf 0xffffffffffc3cf3c

def z29 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x40041831c3c30c30 0x540041831c3c30c3

def z30 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe8051a33c3c30c30 0xfe8051a33c3c30c3

def z31 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x21e518003fff0007 0x021e518003fff000

def z32 : W := mkw 0x0043000a08280280 0x40043000a0828028 0xbde3000e3c3c03c7 0x8bde3000e3c3c03c

def z33 : W := mkw 0x000000000c28a280 0x4000000000c28a28 0x010000001c0c30c2 0x0010000001c0c30c

def z34 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfc071e3fe3ffffff 0xffc071e3fe3fffff

def z35 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0x20e51a32c0000000 0x020e51a32c000000

def z36 : W := mkw 0xa0fff7efa212492f 0x8a0fff7efa212492 0xfeffffffe233cf3d 0xffeffffffe233cf3

def z37 : W := mkw 0x8008004022004800 0x8800800402200480 0x581805c02200cc09 0x6581805c02200cc0

def z38 : W := mkw 0xe1bc67f53752fd27 0x8e1bc67f53752fd2 0xfffee7fd3ff3ff3f 0xffffee7fd3ff3ff3

def z39 : W := mkw 0x0063060a00000004 0x00063060a0000000 0xb8e3060e00000000 0xab8e3060e0000000

def z40 : W := mkw 0xc108005033405c00 0x8c108005033405c0 0x0000000003c00c00 0x00000000003c00c0

def z41 : W := mkw 0xb00868d562d75d71 0xab00868d562d75d7 0xfe1fffffe3ffffff 0xffe1fffffe3fffff

def z42 : W := mkw 0xa0fff7efa212492f 0x8a0fff7efa212492 0x12fae5cc2030c300 0x012fae5cc2030c30

def z43 : W := mkw 0x009c000033000000 0x8009c00003300000 0x79fc00003fc00003 0x079fc00003fc0000

def z44 : W := mkw 0x1000080040850050 0x2100008004085005 0x84011803c00f00f4 0x984011803c00f00f

def z45 : W := mkw 0x00d7d1a58000000b 0x000d7d1a58000000 0xfafff9f1c0000000 0x5fafff9f1c000000

def z46 : W := mkw 0x0020072000000006 0x0002007200000000 0x000007f000000000 0x6000007f00000000

def z47 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x21e402303fc0fc0b 0x021e402303fc0fc0

def z48 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x24051a33c1cc3cfa 0xe24051a33c1cc3cf

def z49 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x20051a32c1cc30c2 0x020051a32c1cc30c

def z50 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x93fbf8003c3f0004 0x193fbf8003c3f000

def z51 : W := mkw 0xc10800503740fc00 0x8c10800503740fc0 0x010000003fc0fc0b 0x0010000003fc0fc0

def z52 : W := mkw 0xd1bc0f7077c5fc56 0xad1bc0f7077c5fc5 0xfdfd1ff3ffcffcff 0xffdfd1ff3ffcffcf

def z53 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x121ae5cc2030c300 0x0121ae5cc2030c30

def z54 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xac051a32c1cc30cf 0xaac051a32c1cc30c

def z55 : W := mkw 0x12dfb8107bff1458 0xf12dfb8107bff145 0xfffffa33ffff3cff 0xffffffa33ffff3cf

def z56 : W := mkw 0xa2dff8c53bbf4929 0xfa2dff8c53bbf492 0xfffffdcd3fffcf3f 0xffffffdcd3fffcf3

def z57 : W := mkw 0x2000608500120121 0x0200060850012012 0xce02e00d02330f3d 0xfce02e00d02330f3

def z58 : W := mkw 0x0000001000401400 0x0000000100040140 0xec04023103c33c3f 0xfec04023103c33c3

def z59 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x68051a32c3cc3ccb 0x668051a32c3cc3cc

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z61 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x4218e1c102030c30 0x54218e1c102030c3

def z62 : W := mkw 0xa06b66cf2e3aeba5 0xca06b66cf2e3aeba 0xfffbe7cf3e3fffff 0xffffbe7cf3e3ffff

def z63 : W := mkw 0xe1bc67f53752fd27 0x8e1bc67f53752fd2 0x7bfce7f13fc3fc3b 0x77bfce7f13fc3fc3

def z64 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8051a33c0000000 0xfe8051a33c000000

def z65 : W := mkw 0x2243f88508bf0129 0x72243f88508bf012 0x8603f80d003f0334 0x98603f80d003f033

def z66 : W := mkw 0x0043d08f88280289 0x40043d08f8828028 0x8603f80fc03c03c4 0x98603f80fc03c03c

def z67 : W := mkw 0x020820003b3a0000 0xd020820003b3a000 0x010000003c300000 0x0010000003c30000

def z68 : W := mkw 0x020828003bbf0000 0xf020828003bbf000 0xe90518003fff0007 0x1e90518003fff000

def z69 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc2030c3d 0xffeffffffc2030c3

def z70 : W := mkw 0x0043080008ad0000 0x60043080008ad000 0xf9e718003fff0007 0x1f9e718003fff000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x1002040c2030c300 0x01002040c2030c30

def z72 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x62fdfbf3c0000000 0x562fdfbf3c000000

def z73 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x21e102021c0c30c2 0x021e102021c0c30c

def z74 : W := mkw 0xc1ff077a3f68fe86 0xcc1ff077a3f68fe8 0xfdff07fe3ffcffcf 0xefdff07fe3ffcffc

def z75 : W := mkw 0x0000408500000001 0x0000040850000000 0x8202e00d00000000 0x98202e00d0000000

def z76 : W := mkw 0xe10860d53752fd21 0x8e10860d53752fd2 0xdf1ae5cd3ff3ff3f 0xfdf1ae5cd3ff3ff3

def z77 : W := mkw 0x0000080000850000 0x2000008000085000 0xe805180003cf0007 0x1e805180003cf000

def z78 : W := mkw 0x8000004000004800 0x0800000400000480 0x000005c00000cc08 0x6000005c00000cc0

def z79 : W := mkw 0x0000001000401400 0x0000000100040140 0x6804023003c03c0b 0x66804023003c03c0

def z80 : W := mkw 0x0043d08f80000009 0x00043d08f8000000 0xda1bfdcfc0000000 0xfda1bfdcfc000000

def z81 : W := mkw 0x51b40f3055c5b456 0x251b40f3055c5b45 0xede51a33dfcf3cff 0xfede51a33dfcf3cf

def z82 : W := mkw 0x1000001040401450 0x0100000104040145 0x00000031c0000c30 0x400000031c0000c3

def z83 : W := mkw 0x020828003bbf0000 0xf020828003bbf000 0x010000003fff0007 0x0010000003fff000

def z84 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc00c30cf 0xffeffffffc00c30c

def z85 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0x7bfcf8003fc30003 0x17bfcf8003fc3000

def z86 : W := mkw 0x00b4072000000006 0x000b407200000000 0x78fc07f000000000 0x678fc07f00000000

def z87 : W := mkw 0xc1ffd7ffb740fc0f 0x8c1ffd7ffb740fc0 0xfbffffffffc0fc0b 0xffbffffffffc0fc0

def z88 : W := mkw 0x0208280033970000 0xb020828003397000 0x0000000003c30000 0x00000000003c3000

def z89 : W := mkw 0xa0fff7efae3aebaf 0xca0fff7efae3aeba 0xfffffffffe3fffff 0xffffffffffe3ffff

def z90 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x0218e1c000000000 0x00218e1c00000000

def z91 : W := mkw 0xc3bcbf7037d7fc0e 0xbc3bcbf7037d7fc0 0x7bfcfff03fc3fc0b 0x77bfcfff03fc3fc0

def z92 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1be7cf223fffff 0xffe1be7cf223ffff

def z93 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x0400000003cf3cff 0x00400000003cf3cf

def z94 : W := mkw 0x00dfb00022120008 0x800dfb0002212000 0xfafff80022330005 0x1fafff8002233000

def z95 : W := mkw 0x000000000c28a280 0x4000000000c28a28 0x9d02040c3c3cf3cf 0xa9d02040c3c3cf3c

def z96 : W := mkw 0x0043d08f80000009 0x00043d08f8000000 0x8203f80fc0000000 0x98203f80fc000000

def z97 : W := mkw 0x0094900000000008 0x0009490000000000 0x421cf80000000000 0x1421cf8000000000

def z98 : W := mkw 0x0043000008280000 0x4004300000828000 0x80030000003c0004 0x080030000003c000

def z99 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbfffffffc30c300 0xffbfffffffc30c30

def z100 : W := mkw 0xa06b66cf2e3aeba5 0xca06b66cf2e3aeba 0x13fae5cc3c30c300 0x013fae5cc3c30c30

def z101 : W := mkw 0xc19c00503740fc00 0x8c19c00503740fc0 0x79fc00003fc0fc0b 0x079fc00003fc0fc0

def z102 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffa33ffff0007 0xffbfffa33ffff000

def z103 : W := mkw 0x0063060a00000004 0x00063060a0000000 0xbce3060e000c30cf 0xabce3060e000c30c

def z104 : W := mkw 0xe12867f52652fd27 0x8e12867f52652fd2 0xde1ae7fd2233ff3d 0xfde1ae7fd2233ff3

def z105 : W := mkw 0x2000608500120121 0x0200060850012012 0x8602e00d00330334 0x98602e00d0033033

def z106 : W := mkw 0xa00040c500004921 0x0a00040c50000492 0xde1ae5cd0000cf38 0xfde1ae5cd0000cf3

def z107 : W := mkw 0x2008608522120121 0x8200860852212012 0xde1ae00d22330335 0x9de1ae00d2233033

def z108 : W := mkw 0x806b064a2e28ea84 0xc806b064a2e28ea8 0xfdfb07ce3e3cffcf 0xefdfb07ce3e3cffc

def z109 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0x13fae5cc3c30c300 0x013fae5cc3c30c30

def z110 : W := mkw 0x00f7972a8c28a28e 0x400f7972a8c28a28 0x21e51a32dc0c30c2 0x021e51a32dc0c30c

def z111 : W := mkw 0x02f79e0a1dada28c 0x702f79e0a1dada28 0x21e51a021dcc30c2 0x021e51a021dcc30c

def z112 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x00041830c1c00000 0x000041830c1c0000

def z113 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xc61ae1cd02330f34 0xdc61ae1cd02330f3

def z114 : W := mkw 0x0043000a08280280 0x40043000a0828028 0x8403000e003c03c4 0x88403000e003c03c

def z115 : W := mkw 0x002047af80000007 0x0002047af8000000 0x000007ffc0000000 0xe000007ffc000000

def z116 : W := mkw 0x02ffffafbbbf000f 0xf02ffffafbbbf000 0xfbffffffffff0007 0xffbffffffffff000

def z117 : W := mkw 0xa008204022124920 0x8a00820402212492 0x040000002233cf3d 0x0040000002233cf3

def z118 : W := mkw 0xe1bc27703752fd26 0x8e1bc27703752fd2 0x7dfc07f03ff3ff3f 0x67dfc07f03ff3ff3

def z119 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x53fef8003ff30000 0x153fef8003ff3000

def z120 : W := mkw 0x02dff88fbbbf0009 0xf02dff88fbbbf000 0xfbfff80fffff0007 0x9fbfff80fffff000

def z121 : W := mkw 0x00630e0a0cada284 0x600630e0a0cada28 0xfde71e0e3ffff3cf 0xbfde71e0e3ffff3c

def z122 : W := mkw 0xa29cf8c533974929 0xba29cf8c53397492 0xde1efdcd23f3cf3d 0xfde1efdcd23f3cf3

def z123 : W := mkw 0x002006000400a004 0x0002006000400a00 0x39e006003c00f00b 0x239e006003c00f00

def z124 : W := mkw 0x00d7900000000008 0x000d790000000000 0xfafff80000000000 0x1fafff8000000000

def z125 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fd1ff3ffc0fc0b 0xff9fd1ff3ffc0fc0

def z126 : W := mkw 0x0000408500000001 0x0000040850000000 0xda1ae5cd00000000 0xfda1ae5cd0000000

def z127 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x8403060e003cf3cc 0xa8403060e003cf3c

def z128 : W := mkw 0x0243b80008bf0008 0x70243b80008bf000 0x8203f800003f0004 0x18203f800003f000

def z129 : W := mkw 0xc12007700440fc06 0x0c12007700440fc0 0x000007f00000fc08 0x6000007f00000fc0

def z130 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x401c01f003c00c00 0x4401c01f003c00c0

def z131 : W := mkw 0x0243f88f88bf0009 0x70243f88f88bf000 0x8203f80fc03f0004 0x98203f80fc03f000

def z132 : W := mkw 0x0020072a80000006 0x00020072a8000000 0x00000232c0000000 0x000000232c000000

def z133 : W := mkw 0x12dfb8107bff1458 0xf12dfb8107bff145 0xfffff8003fff3cff 0x1fffff8003fff3cf

def z134 : W := mkw 0x006b260a2e3aa284 0xc006b260a2e3aa28 0xfffbe60e3e3ff3cf 0xbfffbe60e3e3ff3c

def z135 : W := mkw 0x10630e1a4cedb6d4 0x610630e1a4cedb6d 0xfde71e3fffffffff 0xffde71e3ffffffff

def z136 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x681c03f003c03c0b 0x6681c03f003c03c0

def z137 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1fffffe233cf3d 0xffe1fffffe233cf3

def z138 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x521ae5cd2233cf30 0x5521ae5cd2233cf3

def z139 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x161ae5cc2233cf3d 0x0161ae5cc2233cf3

def z140 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x25e102023c3cf3cf 0x025e102023c3cf3c

def z141 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xda1ae1c122330c35 0x5da1ae1c122330c3

def z142 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffa023fff30cf 0xbfffffa023fff30c

def z143 : W := mkw 0xd1ffdffff7c5fc5f 0xad1ffdffff7c5fc5 0xffffffffffcffcff 0xfffffffffffcffcf

def z144 : W := mkw 0xb008285062d75d70 0xab008285062d75d7 0xec051a33e3ffffff 0xfec051a33e3fffff

def z145 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0xfafffa32c0000000 0x1fafffa32c000000

def z146 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x4618e1c12233cf3d 0x54618e1c12233cf3

def z147 : W := mkw 0x02ffbe0a3fbfa28c 0xf02ffbe0a3fbfa28 0xfffffe0e3ffff3cf 0xbfffffe0e3ffff3c

def z148 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x11f805c03c00c000 0x011f805c03c00c00

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x4800000002000c09 0x64800000002000c0

def z150 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x13fae0003fff0007 0x013fae0003fff000

def z151 : W := mkw 0xc10800503740fc00 0x8c10800503740fc0 0x591805c03fc0fc0b 0x6591805c03fc0fc0

def z152 : W := mkw 0x412007300440b406 0x0412007300440b40 0x0000023000003000 0x0000002300000300

def z153 : W := mkw 0x00d7d08500000009 0x000d7d0850000000 0xfafffdcd00000000 0xffafffdcd0000000

def z154 : W := mkw 0x006306000c28a004 0x4006306000c28a00 0xb9e306003c3cf00f 0x2b9e306003c3cf00

def z155 : W := mkw 0xc12007700440fc06 0x0c12007700440fc0 0x680407f003c0fc0b 0x6680407f003c0fc0

def z156 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x31e3060e3c3cf3c2 0x031e3060e3c3cf3c

def z157 : W := mkw 0xc120077a0440fe86 0x0c120077a0440fe8 0x040007fe0000ffc8 0xe040007fe0000ffc

def z158 : W := mkw 0x0008200022120000 0x8000820002212000 0x0000000022330005 0x0000000002233000

def z159 : W := mkw 0xc10800403700e800 0x8c10800403700e80 0x010000003c00c000 0x0010000003c00c00

def z160 : W := mkw 0x00f7d7bf8040140f 0x000f7d7bf8040140 0xfaffffffc3c03c0b 0xffaffffffc3c03c0

def z161 : W := mkw 0xa008204022124920 0x8a00820402212492 0x0000000002030c30 0x00000000002030c3

def z162 : W := mkw 0x0008200022120000 0x8000820002212000 0xda1ae00022330005 0x1da1ae0002233000

def z163 : W := mkw 0x00d7d1af8000000b 0x000d7d1af8000000 0xc21ff9ffc0000000 0xdc21ff9ffc000000

def z164 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xc21ff80003ff0004 0x1c21ff80003ff000

def z165 : W := mkw 0xd1bc0f7077c5fc56 0xad1bc0f7077c5fc5 0x79fd1ff2ffccfccb 0x679fd1ff2ffccfcc

def z166 : W := mkw 0xe19c61f533525d23 0x8e19c61f533525d2 0x421ce1f103c30c30 0x5421ce1f103c30c3

def z167 : W := mkw 0x0000408500000001 0x0000040850000000 0xde1ae5cd2030c30d 0xfde1ae5cd2030c30

def z168 : W := mkw 0xa04bf0cfa2124929 0x8a04bf0cfa212492 0xde1bfdcfe233cf3d 0xfde1bfdcfe233cf3

def z169 : W := mkw 0x9008085062c55c50 0xa9008085062c55c5 0xfc1d1ff3e3cffcff 0xffc1d1ff3e3cffcf

def z170 : W := mkw 0x8008004022004800 0x8800800402200480 0x401801c002000c00 0x4401801c002000c0

def z171 : W := mkw 0x0063d7af8000000f 0x00063d7af8000000 0x8203ffffc0000000 0xf8203ffffc000000

def z172 : W := mkw 0xa00040c500004921 0x0a00040c50000492 0x040005cd0000cf38 0xe040005cd0000cf3

def z173 : W := mkw 0x0020060a0400a284 0x00020060a0400a28 0x00000202000030c0 0x000000202000030c

def z174 : W := mkw 0x004b20002a3a0000 0xc004b20002a3a000 0xfbfbe0003e3f0007 0x1fbfbe0003e3f000

def z175 : W := mkw 0x002006000400a004 0x0002006000400a00 0x21e002001c003002 0x021e002001c00300

def z176 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x161ae5cd2030cf38 0xe161ae5cd2030cf3

def z177 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xa2e7fa3fc0000000 0x9a2e7fa3fc000000

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802040c00000000 0xa9802040c0000000

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x8402000c00300304 0x88402000c0030030

def z180 : W := mkw 0x8008004022004800 0x8800800402200480 0xdc1a05cc2230cf0d 0xedc1a05cc2230cf0

def z181 : W := mkw 0x0200280008bf0000 0x70200280008bf000 0x00000000003f0004 0x000000000003f000

def z182 : W := mkw 0x020828003bbf0000 0xf020828003bbf000 0xdb1ae0003fff0007 0x1db1ae0003fff000

def z183 : W := mkw 0x02ffbe0a3fbfa28c 0xf02ffbe0a3fbfa28 0xfbfffc0c3fffc307 0x1fbfffc0c3fffc30

def z184 : W := mkw 0xc39cb97033d75c0a 0xbc39cb97033d75c0 0x421cf9f003c30c00 0x5421cf9f003c30c0

def z185 : W := mkw 0xa09cf1e5a212492b 0x8a09cf1e5a212492 0xde1efdfde233cf3d 0xfde1efdfde233cf3

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x39e000003c000003 0x039e000003c00000

def z187 : W := mkw 0x0000408f80000001 0x00000408f8000000 0x0000000fc0000000 0x80000000fc000000

def z188 : W := mkw 0xb00860d562525d71 0x8b00860d562525d7 0xde1ae7ffe233fffd 0xfde1ae7ffe233fff

def z189 : W := mkw 0x8008204022124800 0x8800820402212480 0xda1ae5c02233cc0d 0x7da1ae5c02233cc0

def z190 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x95e3040e3c3cc3c4 0x895e3040e3c3cc3c

def z191 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x68041a31c3c33c3b 0x768041a31c3c33c3

def z192 : W := mkw 0x00f7d7af8400a00f 0x000f7d7af8400a00 0xfbfffffffc00f00b 0xffbfffffffc00f00

def z193 : W := mkw 0x12d7981059ed1458 0x712d7981059ed145 0x21e51a32ddcc30c2 0x021e51a32ddcc30c

def z194 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x44041a33c3c33cf8 0xf44041a33c3c33cf

def z195 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x60051a33c3cf3cf2 0x560051a33c3cf3cf

def z196 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xa4051a33c1cf30f6 0x9a4051a33c1cf30f

def z197 : W := mkw 0x2063668f0c3aa3a5 0x42063668f0c3aa3a 0xbfe3e60f3c3ff3ff 0xbbfe3e60f3c3ff3f

def z198 : W := mkw 0x02df98003bad0008 0xf02df98003bad000 0x79fd18003fcc0003 0x079fd18003fcc000

def z199 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xda1efdfdc0000000 0xfda1efdfdc000000

def z200 : W := mkw 0x0000001000401400 0x0000000100040140 0xe8051a33c3c03c0b 0xfe8051a33c3c03c0

def z201 : W := mkw 0xa2ffffefbbbf492f 0xfa2ffffefbbbf492 0xffffffffffffcf3f 0xfffffffffffffcf3

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804023000000000 0x6680402300000000

def z203 : W := mkw 0x00b447a500000007 0x000b447a50000000 0xfafee7fd00000000 0xffafee7fd0000000

def z204 : W := mkw 0xc3ffbf703ffffc0e 0xfc3ffbf703ffffc0 0xfbfffff03ffffc0f 0x7fbfffff03ffffc0

def z205 : W := mkw 0x80bc076022004806 0x880bc07602200480 0x78fc07f02200cc09 0x678fc07f02200cc0

def z206 : W := mkw 0xc12047ff8440fc07 0x0c12047ff8440fc0 0x000007ffc000fc08 0xe000007ffc000fc0

def z207 : W := mkw 0x00fff7afa212000f 0x800fff7afa212000 0xfaffffffe2330005 0xffaffffffe233000

def z208 : W := mkw 0x1008281062d71450 0xa1008281062d7145 0xfe1ffa33e3ff3cff 0xffe1ffa33e3ff3cf

def z209 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe8051a32c3cf30c7 0x1e8051a32c3cf30c

def z210 : W := mkw 0xc1ff076a3f28ea86 0xcc1ff076a3f28ea8 0xbdfb07ce3c3cf3cf 0xabdfb07ce3c3cf3c

def z211 : W := mkw 0x0043000008280000 0x4004300000828000 0xb9e300003c3c0007 0x0b9e300003c3c000

def z212 : W := mkw 0x0008608522120001 0x8000860852212000 0xda1ae5cd22330005 0xfda1ae5cd2233000

def z213 : W := mkw 0xc1bc0f7037c5fc06 0xac1bc0f7037c5fc0 0xf9fd1ff03fcffc0f 0x7f9fd1ff03fcffc0

def z214 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0x7dfc07f3ffc0fcfb 0xe7dfc07f3ffc0fcf

def z215 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x31fc07f03dc0f002 0x031fc07f03dc0f00

def z216 : W := mkw 0x0000d08580000009 0x00000d0858000000 0x0200f801c0000000 0x10200f801c000000

def z217 : W := mkw 0x0043000a08280280 0x40043000a0828028 0x0002000c00300300 0x00002000c0030030

def z218 : W := mkw 0x00bc072033000006 0x800bc07203300000 0x79fc07f03fc00003 0x679fc07f03fc0000

def z219 : W := mkw 0x0020060a0400a284 0x00020060a0400a28 0x9c02060e2030f3cd 0xa9c02060e2030f3c

def z220 : W := mkw 0x0000408500000001 0x0000040850000000 0xfa1fffffc0000000 0xffa1fffffc000000

def z221 : W := mkw 0xd108085077c5fc50 0xad108085077c5fc5 0x050000003fcffcff 0x0050000003fcffcf

def z222 : W := mkw 0x002006000400a004 0x0002006000400a00 0xbde2060c3c30f30f 0xabde2060c3c30f30

def z223 : W := mkw 0xc1ff077a3f68fe86 0xcc1ff077a3f68fe8 0x79fe07fc3ff0ff0b 0x679fe07fc3ff0ff0

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0xec010203020f3cff 0xfec010203020f3cf

def z225 : W := mkw 0x4194013011401402 0x0419401301140140 0x0004003001c00000 0x00004003001c0000

def z226 : W := mkw 0x0200080019ad0000 0x70200080019ad000 0x010000001dcc0002 0x0010000001dcc000

def z227 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xade102021c0c30cf 0xaade102021c0c30c

def z228 : W := mkw 0x0000080000850000 0x2000008000085000 0x2005180001cc0002 0x02005180001cc000

def z229 : W := mkw 0x0020060a0400a284 0x00020060a0400a28 0x0000040c0000c300 0x00000040c0000c30

def z230 : W := mkw 0xa02046cf0400eba5 0x0a02046cf0400eba 0x040007cf0000fff8 0xe040007cf0000fff

def z231 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x79fc05c03fc0c003 0x079fc05c03fc0c00

def z232 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0x21e518001dcc0002 0x021e518001dcc000

def z233 : W := mkw 0x809c004033004800 0x8809c00403300480 0x79fc05c03fc0cc0b 0x679fc05c03fc0cc0

def z234 : W := mkw 0x00ff060a3f28a284 0xc00ff060a3f28a28 0xfdff060e3ffcf3cf 0xafdff060e3ffcf3c

def z235 : W := mkw 0xe1bc67f53752fd27 0x8e1bc67f53752fd2 0x7bfee7fc3ff0ff0b 0x67bfee7fc3ff0ff0

def z236 : W := mkw 0xb00868c562974971 0xab00868c56297497 0xde1bfdcfe23fcffd 0xfde1bfdcfe23fcff

def z237 : W := mkw 0x0243b000083a0008 0x50243b000083a000 0x0202e00000300000 0x00202e0000030000

def z238 : W := mkw 0x0243b80008bf0008 0x70243b80008bf000 0xea07f80003ff0007 0x1ea07f80003ff000

def z239 : W := mkw 0x22dff8853bbf0129 0xf22dff8853bbf012 0xfffff80d3fff0337 0x9fffff80d3fff033

def z240 : W := mkw 0x029cb8003bbf0008 0xf029cb8003bbf000 0x431cf8003fff0007 0x1431cf8003fff000

def z241 : W := mkw 0x0000000000000000 0x0000000000000000 0x20051a32c0000000 0x020051a32c000000

def z242 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x5a1ae5cc2230cf09 0x65a1ae5cc2230cf0

def z243 : W := mkw 0xe19c61f533525d23 0x8e19c61f533525d2 0xde1ee5fd23f3cf3d 0xfde1ee5fd23f3cf3

def z244 : W := mkw 0x102047bfc0401457 0x0102047bfc040145 0x040007ffc0003cf8 0xe040007ffc0003cf

def z245 : W := mkw 0x00d7900008280008 0x400d790000828000 0xfbfff8003c3c0007 0x1fbfff8003c3c000

def z246 : W := mkw 0x10630e1a4cedb6d4 0x610630e1a4cedb6d 0x21e51a32ddcc30c2 0x021e51a32ddcc30c

def z247 : W := mkw 0xe1ff67ff3f7affa7 0xce1ff67ff3f7affa 0xffffe7ff3fffffff 0xfffffe7ff3ffffff

def z248 : W := mkw 0x1094d9b5c0c5145b 0x21094d9b5c0c5145 0x421cf9f1c3c30c30 0x5421cf9f1c3c30c3

def z249 : W := mkw 0x10630e0a4cada2d4 0x610630e0a4cada2d 0xbde31e0ffc3ff3ff 0xbbde31e0ffc3ff3f

def z250 : W := mkw 0x1094d9b5c0c5145b 0x21094d9b5c0c5145 0xee1dfbf3c3cf3cff 0xfee1dfbf3c3cf3cf

def z251 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x401c07f003c0fc08 0x6401c07f003c0fc0

def z252 : W := mkw 0x0063060a00000004 0x00063060a0000000 0xbce3060e2030c30d 0xabce3060e2030c30

def z253 : W := mkw 0x00ffd7afb300000f 0x800ffd7afb300000 0xfbffffffffc00003 0xffbffffffffc0000

def z254 : W := mkw 0x002006000400a004 0x0002006000400a00 0x000006000000f008 0x2000006000000f00

def z255 : W := mkw 0x00d7d08f80000009 0x000d7d08f8000000 0xfafff80fc0000000 0x9fafff80fc000000

def z256 : W := mkw 0x10630e1a4cedb6d4 0x610630e1a4cedb6d 0xbde71e3efdfcf3cf 0xabde71e3efdfcf3c

def z257 : W := mkw 0x009c200033120000 0x8009c20003312000 0xfbfee0003ff30007 0x1fbfee0003ff3000

def z258 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xcc041831c3c30c3d 0xfcc041831c3c30c3

def z259 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x39e2060c3c30f30b 0x239e2060c3c30f30

def z260 : W := mkw 0x0063d68f8000000d 0x00063d68f8000000 0xbae3fe0fc0000000 0xbbae3fe0fc000000

def z261 : W := mkw 0x02f79f2a99ad000e 0x702f79f2a99ad000 0x21e51a32ddcc0002 0x021e51a32ddcc000

def z262 : W := mkw 0x02f7dfaf99ad000f 0x702f7dfaf99ad000 0xfbffffffddcc0002 0xffbffffffddcc000

def z263 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xc4051833c3cf0cf4 0xdc4051833c3cf0cf

def z264 : W := mkw 0xc10800503740fc00 0x8c10800503740fc0 0x690402303fc0fc0b 0x6690402303fc0fc0

def z265 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfc07f13fc3fc3f 0xffdfc07f13fc3fc3

def z266 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000002030c30d 0x0040000002030c30

def z267 : W := mkw 0x0020060a0400a284 0x00020060a0400a28 0x0400060e0000f3c8 0xa0400060e0000f3c

def z268 : W := mkw 0xc3ffbf7a3ffffe8e 0xfc3ffbf7a3ffffe8 0xfffffffe3fffffcf 0xffffffffe3fffffc

def z269 : W := mkw 0x2000608500120121 0x0200060850012012 0x9e02e40d2033c33d 0xb9e02e40d2033c33

def z270 : W := mkw 0xa00040c500004921 0x0a00040c50000492 0x000005cc0000c300 0x0000005cc0000c30

def z271 : W := mkw 0x43f79f301dedb40e 0x743f79f301dedb40 0x21e51a301dcc3002 0x021e51a301dcc300

def z272 : W := mkw 0x10f7dfbfc0c5145f 0x210f7dfbfc0c5145 0xfaffffffc3c30c30 0xffaffffffc3c30c3

def z273 : W := mkw 0xa008204022124920 0x8a00820402212492 0x5c1805c02233cf3d 0x65c1805c02233cf3

def z274 : W := mkw 0xa00060c500124921 0x0a00060c50012492 0x8602e5cd0033cf3c 0xf8602e5cd0033cf3

def z275 : W := mkw 0xa00040c500004921 0x0a00040c50000492 0x000001c100000c30 0x4000001c100000c3

def z276 : W := mkw 0xa29cf8c533974929 0xba29cf8c53397492 0x421cf9c103c30c30 0x5421cf9c103c30c3

def z277 : W := mkw 0x129cb81073d71458 0xb129cb81073d7145 0xee1dfa33c3cf3cff 0xfee1dfa33c3cf3cf

def z278 : W := mkw 0x002047af8400a287 0x0002047af8400a28 0x040007ffc000f3c8 0xe040007ffc000f3c

def z279 : W := mkw 0x0008200022120000 0x8000820002212000 0x4218e00002030000 0x14218e0000203000

def z280 : W := mkw 0xa00040c500004921 0x0a00040c50000492 0x9c0205cd2030cf3d 0xe9c0205cd2030cf3

def z281 : W := mkw 0x0000001000401400 0x0000000100040140 0x0000000003c03c0b 0x00000000003c03c0

def z282 : W := mkw 0x41b407201500a006 0x041b407201500a00 0x01e000001c000000 0x001e000001c00000

def z283 : W := mkw 0x80ffd7efa200480f 0x880ffd7efa200480 0xfaffffffe200cc09 0xffaffffffe200cc0

def z284 : W := mkw 0x02d7b80019bf0008 0x702d7b80019bf000 0xa3e7f8001dff0006 0x1a3e7f8001dff000

def z285 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xda1ae5cd2030c300 0xfda1ae5cd2030c30

def z286 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0xe8e51a33c0000000 0xfe8e51a33c000000

def z287 : W := mkw 0x02dfb80a3bbf0288 0xf02dfb80a3bbf028 0xfffff80e3fff03c7 0x9fffff80e3fff03c

def z288 : W := mkw 0xa04b60cf2a3a4ba1 0xca04b60cf2a3a4ba 0xde1be5cf223fcffd 0xfde1be5cf223fcff

def z289 : W := mkw 0x1000000040000050 0x0100000004000005 0x04000003c00000f0 0x804000003c00000f

def z290 : W := mkw 0x12dfb8107bff1458 0xf12dfb8107bff145 0xfbfffa32ffff30c7 0x1fbfffa32ffff30c

def z291 : W := mkw 0x10f7dfafc085005f 0x210f7dfafc085005 0xfeffffffc00f00f4 0xffeffffffc00f00f

def z292 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfffff803ffff00f7 0x9fffff803ffff00f

def z293 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x51fc05f03fc0cc00 0x451fc05f03fc0cc0

def z294 : W := mkw 0x82dfb8403bbf4808 0xf82dfb8403bbf480 0xfbfffdc03fffcc0f 0x7fbfffdc03fffcc0

def z295 : W := mkw 0x00f7072a00000006 0x000f7072a0000000 0xf8ff07fe00000000 0xef8ff07fe0000000

def z296 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x961ae5cd2033c334 0x9961ae5cd2033c33

def z297 : W := mkw 0xc12007700440fc06 0x0c12007700440fc0 0x39e007f03c00fc0b 0x639e007f03c00fc0

def z298 : W := mkw 0xc1b407701540fc06 0x0c1b407701540fc0 0x21e407f01dc0fc0a 0x621e407f01dc0fc0

def z299 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb9e302023c3c30c7 0x0b9e302023c3c30c

def z300 : W := mkw 0x0043000008280000 0x4004300000828000 0x11e200003c300000 0x011e200003c30000

def z301 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0xfbfff8001dcc0002 0x1fbfff8001dcc000

def z302 : W := mkw 0x2000608500120121 0x0200060850012012 0x0202e00c00300300 0x00202e00c0030030

def z303 : W := mkw 0x10f7dfbfc0c5145f 0x210f7dfbfc0c5145 0xfeffffffc3cf3cff 0xffeffffffc3cf3cf

def z304 : W := mkw 0xc1bc27703752fc06 0x8c1bc27703752fc0 0xfbfee7f03ff3fc0f 0x7fbfee7f03ff3fc0

def z305 : W := mkw 0x002006000400a004 0x0002006000400a00 0x11e004003c00c000 0x011e004003c00c00

def z306 : W := mkw 0x0008200022120000 0x8000820002212000 0xde1ae40c2233c30d 0xbde1ae40c2233c30

def z307 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x15e2060e3c30f3c8 0xa15e2060e3c30f3c

def z308 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffc0c3fffc30f 0xbfffffc0c3fffc30

def z309 : W := mkw 0x00b407200400a006 0x000b407200400a00 0x79fc07f03c00f00b 0x679fc07f03c00f00

def z310 : W := mkw 0x00f7d7af8828000f 0x400f7d7af8828000 0xfbfffffffc3c0007 0xffbfffffffc3c000

def z311 : W := mkw 0x0000000000000000 0x0000000000000000 0xe805180000000000 0x1e80518000000000

def z312 : W := mkw 0x02ffbe0a3bbf000c 0xf02ffbe0a3bbf000 0xfbfffe0e3fff0007 0xbfbfffe0e3fff000

def z313 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xce18e1c102030c3d 0xfce18e1c102030c3

def z314 : W := mkw 0x1043d89fc0c51459 0x21043d89fc0c5145 0xee07fa3fc3cf3cff 0xfee07fa3fc3cf3cf

def z315 : W := mkw 0xa09cf1e5a212492b 0x8a09cf1e5a212492 0x421cf9f1c2030c30 0x5421cf9f1c2030c3

def z316 : W := mkw 0x2000200000120120 0x0200020000012012 0x0400000000330334 0x0040000000033033

def z317 : W := mkw 0x0000408500000001 0x0000040850000000 0xde1ae5cd02030c3d 0xfde1ae5cd02030c3

def z318 : W := mkw 0x00f7dfaf8085000f 0x200f7dfaf8085000 0xfaffffffc3cf0007 0xffaffffffc3cf000

def z319 : W := mkw 0x0263be0a0cbfa28c 0x70263be0a0cbfa28 0xbfe3fe0e3c3ff3cf 0xbbfe3fe0e3c3ff3c

def z320 : W := mkw 0x20f7f7af8012012f 0x020f7f7af8012012 0xfeffffffc0330334 0xffeffffffc033033

def z321 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x04000233c3cf3cff 0xe04000233c3cf3cf

def z322 : W := mkw 0x1243b81048ff1458 0x71243b81048ff145 0xee07fa33c3ff3cff 0xfee07fa33c3ff3cf

def z323 : W := mkw 0xc1f7d7ff8440fc0f 0x0c1f7d7ff8440fc0 0xfaffffffc000fc08 0xffaffffffc000fc0

def z324 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x32fffffec0000000 0x032fffffec000000

def z325 : W := mkw 0x0000001000401400 0x0000000100040140 0x2004023001c03002 0x02004023001c0300

def z326 : W := mkw 0x0063060a08280284 0x40063060a0828028 0xbce3060e003c03c4 0xabce3060e003c03c

def z327 : W := mkw 0x0000001000401400 0x0000000100040140 0x0000023000003c08 0x60000023000003c0

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c0000000000000d 0xa8c0000000000000

def z329 : W := mkw 0x3000689540d71571 0x23000689540d7157 0xee07fa3fc3ff3fff 0xfee07fa3fc3ff3ff

def z330 : W := mkw 0xc1ff07703f68fc06 0xcc1ff07703f68fc0 0xf9ff07f03ffcfc0f 0x6f9ff07f03ffcfc0

def z331 : W := mkw 0xb0ffffffe2d75d7f 0xab0ffffffe2d75d7 0xfeffffffe3ffffff 0xffeffffffe3fffff

def z332 : W := mkw 0x00f7972a8c28a28e 0x400f7972a8c28a28 0xbde71e3efc3cf3cf 0xabde71e3efc3cf3c

def z333 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb9e3040c3c3cc307 0x0b9e3040c3c3cc30

def z334 : W := mkw 0x8008004022004800 0x8800800402200480 0x101805c02000c000 0x0101805c02000c00

def z335 : W := mkw 0xa06b66cf22124925 0x8a06b66cf2212492 0xfefbe7cf2233cf3d 0xffefbe7cf2233cf3

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000000000c30cf 0x004000000000c30c

def z337 : W := mkw 0x0043900000000008 0x0004390000000000 0x8203f80000000000 0x18203f8000000000

def z338 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xcc00000103cf3cff 0xfcc00000103cf3cf

def z339 : W := mkw 0xc1ffd7efb700e80f 0x8c1ffd7efb700e80 0x13fae5cc3c00c000 0x013fae5cc3c00c00

def z340 : W := mkw 0xc1ffd7ffbf68fe8f 0xcc1ffd7ffbf68fe8 0xfffffffffffcffcf 0xffffffffffffcffc

def z341 : W := mkw 0x00b4d7a58000000f 0x000b4d7a58000000 0x7afcfff1c0000000 0x77afcfff1c000000

def z342 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xda1ae5cc2233c305 0x1da1ae5cc2233c30

def z343 : W := mkw 0x43ffbf303fffb40e 0xf43ffbf303fffb40 0xfbfffa303fff3007 0x1fbfffa303fff300

def z344 : W := mkw 0x0000000008280280 0x4000000000828028 0x04000000003c03c4 0x004000000003c03c

def z345 : W := mkw 0x1000080040850050 0x2100008004085005 0xec051a33c00f00f4 0xfec051a33c00f00f

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x581805c000000000 0x6581805c00000000

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x6804000003c00003 0x06804000003c0000

def z348 : W := mkw 0x0000001000401400 0x0000000100040140 0xec05023203cc3ccf 0xeec05023203cc3cc

def z349 : W := mkw 0x00d7900000000008 0x000d790000000000 0xfafffa33c0000000 0xffafffa33c000000

def z350 : W := mkw 0xa0f7d7ef8000492f 0x0a0f7d7ef8000492 0xfeffffffc000cf38 0xffeffffffc000cf3

def z351 : W := mkw 0xa2dfb8403bbf4928 0xfa2dfb8403bbf492 0xfffff8003fffcf3f 0x1fffff8003fffcf3

def z352 : W := mkw 0xa0bc67e522124927 0x8a0bc67e52212492 0xfefee7fd2233cf3d 0xffefee7fd2233cf3

def z353 : W := mkw 0xc1bc077a3740fe86 0x8c1bc077a3740fe8 0x7dfc07fe3fc0ffcb 0xe7dfc07fe3fc0ffc

def z354 : W := mkw 0x41f7073a1d68b686 0x441f7073a1d68b68 0x21e502321dcc30c2 0x021e502321dcc30c

def z355 : W := mkw 0x0094000000000000 0x0009400000000000 0x78fc000000000000 0x078fc00000000000

def z356 : W := mkw 0xc163077a0c68fe86 0x4c163077a0c68fe8 0xbde307fe3c3cffcf 0xebde307fe3c3cffc

def z357 : W := mkw 0x0063060a08280004 0x40063060a0828000 0xb9e3060e3c3c0007 0xab9e3060e3c3c000

def z358 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x44041831c3cf3cff 0x544041831c3cf3cf

def z359 : W := mkw 0xa02047ef80004927 0x0a02047ef8000492 0x040007ffc000cf38 0xe040007ffc000cf3

def z360 : W := mkw 0x41f7073a1d68b686 0x441f7073a1d68b68 0xbde7063e3dfcf3cf 0xabde7063e3dfcf3c

def z361 : W := mkw 0x000000000c28a280 0x4000000000c28a28 0x050000003c3cf3cf 0x0050000003c3cf3c

def z362 : W := mkw 0xa04b60c52a3a4921 0xca04b60c52a3a492 0xfffbe5cd3e3fcf3f 0xffffbe5cd3e3fcf3

def z363 : W := mkw 0xb06b6edf6efffff5 0xeb06b6edf6efffff 0xffffffffffffffff 0xffffffffffffffff

def z364 : W := mkw 0xa20828403bbf4920 0xfa20828403bbf492 0x050000003fffcf3f 0x0050000003fffcf3

def z365 : W := mkw 0xb00048d540c55d71 0x2b00048d540c55d7 0xec051fffc3cfffff 0xfec051fffc3cffff

def z366 : W := mkw 0x00b447af80000007 0x000b447af8000000 0x78fc07ffc0000000 0xe78fc07ffc000000

def z367 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde3060f3e3fffff 0xffde3060f3e3ffff

def z368 : W := mkw 0xa06b66cf2e3aeba5 0xca06b66cf2e3aeba 0xbffbe7ce3c3cf3cf 0xabffbe7ce3c3cf3c

def z369 : W := mkw 0x000000000c28a280 0x4000000000c28a28 0xad0102023c3cf3cf 0xaad0102023c3cf3c

def z370 : W := mkw 0xd1bc0f7077c5fc56 0xad1bc0f7077c5fc5 0x79fc1ff1ffc3fc3b 0x779fc1ff1ffc3fc3

def z371 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x63fdf8001fcf0002 0x163fdf8001fcf000

def z372 : W := mkw 0x00f7d7af8828028f 0x400f7d7af8828028 0xfeffffffc03c03c4 0xffeffffffc03c03c

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000100000c38 0xe0400000100000c3

def z374 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0x7bfee0003ff00003 0x07bfee0003ff0000

def z375 : W := mkw 0x02ffffafbfbfa28f 0xf02ffffafbfbfa28 0xfffffffffffff3cf 0xffffffffffffff3c

def z376 : W := mkw 0x02dff9a5bbbf000b 0xf02dff9a5bbbf000 0xfbfff9f1ffff0007 0x5fbfff9f1ffff000

def z377 : W := mkw 0x100008104cedb6d0 0x6100008104cedb6d 0x050000003fffffff 0x0050000003ffffff

def z378 : W := mkw 0x00f7960a0c28a28c 0x400f7960a0c28a28 0xfffffe0e3c3cf3cf 0xbfffffe0e3c3cf3c

def z379 : W := mkw 0x10f7dfbfccedb6df 0x610f7dfbfccedb6d 0xffffffffffffffff 0xffffffffffffffff

def z380 : W := mkw 0x00f7d7af8400a28f 0x000f7d7af8400a28 0xfeffffffc000f3c8 0xffeffffffc000f3c

def z381 : W := mkw 0x002047af80000007 0x0002047af8000000 0xda1ae7ffc0000000 0xfda1ae7ffc000000

def z382 : W := mkw 0xc1ffd7ffb3405c0f 0x8c1ffd7ffb3405c0 0xfaffffffc3c00c00 0xffaffffffc3c00c0

def z383 : W := mkw 0x0020060a0c28a284 0x40020060a0c28a28 0x0500060e3c3cf3cf 0xa0500060e3c3cf3c

def z384 : W := mkw 0x002047af80000007 0x0002047af8000000 0xe8051fffc0000000 0xfe8051fffc000000

def z385 : W := mkw 0x10d7981040c51458 0x210d7981040c5145 0xfefffa33c3cf3cff 0xffefffa33c3cf3cf

def z386 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0x00e0000000000000 0x000e000000000000

def z387 : W := mkw 0x006347af8c28a287 0x4006347af8c28a28 0xbde307fffc3cf3cf 0xebde307fffc3cf3c

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x9802000020300005 0x0980200002030000

def z389 : W := mkw 0x0000080000850000 0x2000008000085000 0xe8051a33c3cf0007 0xfe8051a33c3cf000

def z390 : W := mkw 0x026b2e0a3fbfa284 0xf026b2e0a3fbfa28 0xbde3060e3ffff3cf 0xabde3060e3ffff3c

def z391 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde71e3ffc3cf3cf 0xffde71e3ffc3cf3c

def z392 : W := mkw 0x1000001040401450 0x0100000104040145 0x6c040233c3c03cfb 0xe6c040233c3c03cf

def z393 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0xb9e718003dfc0007 0x0b9e718003dfc000

def z394 : W := mkw 0x10630e1a4cedb6d4 0x610630e1a4cedb6d 0xbde3060e3fffffff 0xabde3060e3ffffff

def z395 : W := mkw 0x0063061a0c68b684 0x40063061a0c68b68 0xfde7063e3ffcffcf 0xefde7063e3ffcffc

def z396 : W := mkw 0x2043608f083a03a1 0x42043608f083a03a 0x8603e00f003f03f4 0x98603e00f003f03f

def z397 : W := mkw 0x024bb8003bbf0008 0xf024bb8003bbf000 0x8303f8003fff0007 0x18303f8003fff000

def z398 : W := mkw 0xc1bc47ffb740fc07 0x8c1bc47ffb740fc0 0x79fc07ffffc0fc0b 0xe79fc07ffffc0fc0

def z399 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x0000000001cc30c2 0x00000000001cc30c

def z400 : W := mkw 0x1063061a4c68b6d4 0x41063061a4c68b6d 0xbde3063ffc3cffff 0xebde3063ffc3cfff

def z401 : W := mkw 0x1000080040850050 0x2100008004085005 0xec051803c3cf00f7 0x9ec051803c3cf00f

def z402 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x8602e00d2233cf3d 0x98602e00d2233cf3

def z403 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0x78fd1ff2c0000000 0x678fd1ff2c000000

def z404 : W := mkw 0x00b4d7af8000000f 0x000b4d7af8000000 0x421cffffc0000000 0xf421cffffc000000

def z405 : W := mkw 0x1020061a4440b6d4 0x01020061a4440b6d 0x0400063fc000fff8 0xe0400063fc000fff

def z406 : W := mkw 0x12ffffbffbff145f 0xf12ffffbffbff145 0xffffffffffff3cff 0xfffffffffffff3cf

def z407 : W := mkw 0xc19c01703740fc02 0x8c19c01703740fc0 0x411c01f03fc0fc0b 0x4411c01f03fc0fc0

def z408 : W := mkw 0x10f79f3ac0c5145e 0x210f79f3ac0c5145 0xece51a33c3cf3cff 0xfece51a33c3cf3cf

def z409 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x61fc03f01fc03c02 0x461fc03f01fc03c0

def z410 : W := mkw 0x10204fbfc0c51457 0x210204fbfc0c5145 0xec051fffc3cf3cff 0xfec051fffc3cf3cf

def z411 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe8051a33c1cc30c2 0xfe8051a33c1cc30c

def z412 : W := mkw 0xc10800503f68fe80 0xcc10800503f68fe8 0x050000003ffcffcf 0x0050000003ffcffc

def z413 : W := mkw 0xa008204022124920 0x8a00820402212492 0xcc0000012233cf3d 0xfcc0000012233cf3

def z414 : W := mkw 0x0000080000850000 0x2000008000085000 0x80011800000f0004 0x180011800000f000

def z415 : W := mkw 0x02f7ffaf88bf000f 0x702f7ffaf88bf000 0xfaffffffc03f0004 0xffaffffffc03f000

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0xa801020200000000 0xaa80102020000000

def z417 : W := mkw 0x0020060000000004 0x0002006000000000 0x38e0060000000000 0x238e006000000000

def z418 : W := mkw 0xb00868d562d75d71 0xab00868d562d75d7 0xde1efdfde3f3cf3d 0xfde1efdfde3f3cf3

def z419 : W := mkw 0x02fff7afbb3a000f 0xd02fff7afbb3a000 0x13fae5cc3c300000 0x013fae5cc3c30000

def z420 : W := mkw 0xc1ff077a3740fc06 0x8c1ff077a3740fc0 0xf9ff07fe3fc0fc0b 0xef9ff07fe3fc0fc0

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x20010202000c30c2 0x020010202000c30c

def z422 : W := mkw 0x00d7900000000008 0x000d790000000000 0x20e5180000000000 0x020e518000000000

def z423 : W := mkw 0xa02866cf2612eba5 0x8a02866cf2612eba 0xde1ae7cf2233fffd 0xfde1ae7cf2233fff

def z424 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x52fefdfdc0000000 0x552fefdfdc000000

def z425 : W := mkw 0x0063060a00000004 0x00063060a0000000 0xf8e71e3fc0000000 0xff8e71e3fc000000

def z426 : W := mkw 0xd108085077c5fc50 0xad108085077c5fc5 0xed051a33ffcffcff 0xfed051a33ffcffcf

def z427 : W := mkw 0x009c001033401400 0x8009c00103340140 0x79fc02303fc03c0b 0x679fc02303fc03c0

def z428 : W := mkw 0xd19c097073c55c52 0xad19c097073c55c5 0x401c19f1c3c30c30 0x5401c19f1c3c30c3

def z429 : W := mkw 0x0063468f0c28a285 0x40063468f0c28a28 0xfffbe7cf3c3cf3cf 0xffffbe7cf3c3cf3c

def z430 : W := mkw 0x0043000a0c28a280 0x40043000a0c28a28 0x8503000e3c3cf3cf 0x88503000e3c3cf3c

def z431 : W := mkw 0x0020060a00000004 0x00020060a0000000 0x0000060e00000000 0xa0000060e0000000

def z432 : W := mkw 0x1043080a48ad02d0 0x61043080a48ad02d 0x8403180fc03f03f4 0x98403180fc03f03f

def z433 : W := mkw 0x02fff7afbb3a000f 0xd02fff7afbb3a000 0xfbfffffffc300000 0xffbfffffffc30000

def z434 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x20e51fffc0000000 0xe20e51fffc000000

def z435 : W := mkw 0x12dfb8107bff1458 0xf12dfb8107bff145 0xfbfff831ffff0c37 0x5fbfff831ffff0c3

def z436 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0xda1ef80023f30005 0x1da1ef80023f3000

def z437 : W := mkw 0x002047af80000007 0x0002047af8000000 0x000005cc00000000 0x0000005cc0000000

def z438 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x79fc07f01dc03002 0x679fc07f01dc0300

def z439 : W := mkw 0xc3ff9f703fedfc0e 0xfc3ff9f703fedfc0 0x79fd1ff03fccfc0b 0x679fd1ff03fccfc0

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x40041831c0000000 0x540041831c000000

def z441 : W := mkw 0x129cb81073d71458 0xb129cb81073d7145 0x421cf831c3c30c30 0x5421cf831c3c30c3

def z442 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x11f805c03fc0fc0b 0x011f805c03fc0fc0

def z443 : W := mkw 0x0000080000850000 0x2000008000085000 0x0000000003cf0007 0x00000000003cf000

def z444 : W := mkw 0x8008004022004800 0x8800800402200480 0x000000002200cc09 0x0000000002200cc0

def z445 : W := mkw 0xc19cd1f5b3405c0b 0x8c19cd1f5b3405c0 0x421cf9f1c3c00c00 0x5421cf9f1c3c00c0

def z446 : W := mkw 0x0000408500000001 0x0000040850000000 0x4218e1c100000000 0x54218e1c10000000

def z447 : W := mkw 0x00d7900000000008 0x000d790000000000 0x12fae00000000000 0x012fae0000000000

def z448 : W := mkw 0xc12807702640fc06 0x8c12807702640fc0 0x581807f02200fc09 0x6581807f02200fc0

def z449 : W := mkw 0x0000200000120000 0x0000020000012000 0x8202e00000330004 0x18202e0000033000

def z450 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x92fbfdcfc0000000 0x992fbfdcfc000000

def z451 : W := mkw 0xa00860c52e3aeba1 0xca00860c52e3aeba 0xdf1ae5cd3e3fffff 0xfdf1ae5cd3e3ffff

def z452 : W := mkw 0xa000004000004920 0x0a00000400000492 0x040000000000cf38 0x0040000000000cf3

def z453 : W := mkw 0xc1ff977ab740fc0e 0x8c1ff977ab740fc0 0x79fd1ff2ffc0fc0b 0x679fd1ff2ffc0fc0

def z454 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x12fae7ffc0000000 0xe12fae7ffc000000

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc03060e203cf3cf 0xabc03060e203cf3c

def z456 : W := mkw 0xe1bc67e53712e927 0x8e1bc67e53712e92 0xdffae5cd3e33cf3d 0xfdffae5cd3e33cf3

def z457 : W := mkw 0xe12047f50440fd27 0x0e12047f50440fd2 0x040007fd0000ff38 0xe040007fd0000ff3

def z458 : W := mkw 0x0094012000000002 0x0009401200000000 0x401c01f000000000 0x4401c01f00000000

def z459 : W := mkw 0xe1bc47f53740fd27 0x8e1bc47f53740fd2 0x7dfc07fd3fc0ff3b 0xe7dfc07fd3fc0ff3

def z460 : W := mkw 0x0294980011850008 0x3029498001185000 0x0004180001c00000 0x00004180001c0000

def z461 : W := mkw 0x0008280022970000 0xa000828002297000 0xfa1ff80023ff0007 0x1fa1ff80023ff000

def z462 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0xb8e71e3ec0000000 0xab8e71e3ec000000

def z463 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xea1dfbf3c0000000 0xfea1dfbf3c000000

def z464 : W := mkw 0x00b4072000000006 0x000b407200000000 0x20e4023000000000 0x020e402300000000

def z465 : W := mkw 0x0043000000000000 0x0004300000000000 0xb8e3000000000000 0x0b8e300000000000

def z466 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbffffffdc0c30c2 0xffbffffffdc0c30c

def z467 : W := mkw 0xb008285062d75d70 0xab008285062d75d7 0x0400000023ffffff 0x00400000023fffff

def z468 : W := mkw 0xa06b264a2e3aeba4 0xca06b264a2e3aeba 0xbde3060e3e3fffff 0xabde3060e3e3ffff

def z469 : W := mkw 0x51b40f3055c5b456 0x251b40f3055c5b45 0x21e51a32ddcc30c2 0x021e51a32ddcc30c

def z470 : W := mkw 0x024bb8002abf0008 0xf024bb8002abf000 0xda1bf800223f0005 0x1da1bf800223f000

def z471 : W := mkw 0x00df00003b280000 0xc00df00003b28000 0xf9ff00003ffc0007 0x0f9ff00003ffc000

def z472 : W := mkw 0x1000001040401450 0x0100000104040145 0x0400000000003cf8 0x00400000000003cf

def z473 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x0218e1c000000000 0x00218e1c00000000

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0xda1ae00000000000 0x1da1ae0000000000

def z475 : W := mkw 0x0063060a0400a284 0x00063060a0400a28 0xbce3060e0000f3c8 0xabce3060e0000f3c

def z476 : W := mkw 0xa0fff7efa212492f 0x8a0fff7efa212492 0xdefae5cd2233cf3d 0xfdefae5cd2233cf3

def z477 : W := mkw 0x10b40f3040c51456 0x210b40f3040c5145 0xfcfd1ff3c3cf3cff 0xffcfd1ff3c3cf3cf

def z478 : W := mkw 0x0063060a00000004 0x00063060a0000000 0x10e2040c00000000 0x010e2040c0000000

def z479 : W := mkw 0x0043000a00000000 0x00043000a0000000 0x8003000e00000000 0x88003000e0000000

def z480 : W := mkw 0xd19c097073c55c52 0xad19c097073c55c5 0xec1d1bf3c3cf3cff 0xfec1d1bf3c3cf3cf

def z481 : W := mkw 0xd1ff0f7a7fedfed6 0xed1ff0f7a7fedfed 0xfdff1fffffffffff 0xffdff1ffffffffff

def z482 : W := mkw 0x029cf9a5b397000b 0xb029cf9a5b397000 0x421cf9f1c3c30000 0x5421cf9f1c3c3000

def z483 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x84011803c3cf3cff 0x984011803c3cf3cf

def z484 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfafffdcc00000000 0x1fafffdcc0000000

def z485 : W := mkw 0x1000001040401450 0x0100000104040145 0xec051a33c0003cf8 0xfec051a33c0003cf

def z486 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x7afee7fc00000000 0x67afee7fc0000000

def z487 : W := mkw 0xa2dff0c53b3a4929 0xda2dff0c53b3a492 0x13fae5cc3c30c300 0x013fae5cc3c30c30

def z488 : W := mkw 0x000000000400a280 0x0000000000400a28 0x040000000000f3c8 0x0040000000000f3c

def z489 : W := mkw 0xc1bc47f53740fc07 0x8c1bc47f53740fc0 0xfbfee7fd3fc0fc0b 0xffbfee7fd3fc0fc0

def z490 : W := mkw 0xf1bc6ff577d7fd77 0xaf1bc6ff577d7fd7 0xffffffffffffffff 0xffffffffffffffff

def z491 : W := mkw 0x41f7973a9540b40e 0x041f7973a9540b40 0x21e51a32ddc03002 0x021e51a32ddc0300

def z492 : W := mkw 0x2000608500120121 0x0200060850012012 0xde1ae5cd00330334 0xfde1ae5cd0033033

def z493 : W := mkw 0xa008204022124920 0x8a00820402212492 0x9c02040c2233cf3d 0xa9c02040c2233cf3

def z494 : W := mkw 0x1000080040850050 0x2100008004085005 0x04000000000f00f4 0x004000000000f00f

def z495 : W := mkw 0x0043d08f80000009 0x00043d08f8000000 0xea07fa3fc0000000 0xfea07fa3fc000000

def z496 : W := mkw 0x10200e1044c5b454 0x210200e1044c5b45 0xfde51e33ffcffcff 0xffde51e33ffcffcf

def z497 : W := mkw 0x0243980008ad0008 0x70243980008ad000 0x00011800000c0000 0x000011800000c000

def z498 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x4618e5cd0203cf38 0xf4618e5cd0203cf3

def z499 : W := mkw 0xa0fff7efa212492f 0x8a0fff7efa212492 0xfaffffffc2030c30 0xffaffffffc2030c3

def z500 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x15e2040c3c3cf3cf 0x015e2040c3c3cf3c

def z501 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xbafbe7ce00000000 0xabafbe7ce0000000

def z502 : W := mkw 0x0000001000401400 0x0000000100040140 0x4004003003c00c00 0x44004003003c00c0

def z503 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x39f807c03c00f00b 0x239f807c03c00f00

def z504 : W := mkw 0xa02866c52612e925 0x8a02866c52612e92 0xfffae7cd3e33ff3f 0xffffae7cd3e33ff3

def z505 : W := mkw 0xd3ffbf707ffffc5e 0xfd3ffbf707ffffc5 0xfffffff3fffffcff 0xffffffff3fffffcf

def z506 : W := mkw 0x100008104cedb6d0 0x6100008104cedb6d 0xed051a33ffffffff 0xfed051a33fffffff

def z507 : W := mkw 0x00f7960a0000000c 0x000f7960a0000000 0xfafffe0e00000000 0xbfafffe0e0000000

def z508 : W := mkw 0x020828003fbfa280 0xf020828003fbfa28 0x050000003ffff3cf 0x0050000003ffff3c

def z509 : W := mkw 0x02ffffafb397000f 0xb02ffffafb397000 0xfaffffffc3c30000 0xffaffffffc3c3000

def z510 : W := mkw 0xa06b66cf2e3aeba5 0xca06b66cf2e3aeba 0xdffae5cd3e33cf3d 0xfdffae5cd3e33cf3

def z511 : W := mkw 0x0063060a0400a004 0x00063060a0400a00 0xb9e3060e3c00f00b 0xab9e3060e3c00f00

def z512 : W := mkw 0xa00840c522004921 0x8a00840c52200492 0x5c1805cd2200cf39 0xe5c1805cd2200cf3

def z513 : W := mkw 0x0000408500000001 0x0000040850000000 0x121ae5cc00000000 0x0121ae5cc0000000

def z514 : W := mkw 0x02dfb8103bff1408 0xf02dfb8103bff140 0xfbfffa303fff3c0f 0x7fbfffa303fff3c0

def z515 : W := mkw 0x3000688540970171 0x2300068854097017 0x8603f80fc03f03f4 0x98603f80fc03f03f

def z516 : W := mkw 0x006347af80000007 0x0006347af8000000 0xb8e307ffc0000000 0xeb8e307ffc000000

def z517 : W := mkw 0x000000000400a000 0x0000000000400a00 0x010000003c00f00b 0x0010000003c00f00

def z518 : W := mkw 0xc1bcd7f5b740fc0f 0x8c1bcd7f5b740fc0 0x7bfcfff1ffc0fc0b 0x77bfcfff1ffc0fc0

def z519 : W := mkw 0xc100017000405c02 0x0c100017000405c0 0x000001f000000c00 0x4000001f000000c0

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000002030005 0x1c80000000203000

def z521 : W := mkw 0xa008204022124920 0x8a00820402212492 0xde1ae0002233cf3d 0x1de1ae0002233cf3

def z522 : W := mkw 0x0000080000850000 0x2000008000085000 0xec051a0203cf30cf 0xbec051a0203cf30c

def z523 : W := mkw 0x02ffbf203bbf000e 0xf02ffbf203bbf000 0xfbfffff03fff0007 0x7fbfffff03fff000

def z524 : W := mkw 0xb2dff8d57bff5d79 0xfb2dff8d57bff5d7 0xffffffffffffffff 0xffffffffffffffff

def z525 : W := mkw 0xb00868d562d75d71 0xab00868d562d75d7 0x421cf9f1c3c30c30 0x5421cf9f1c3c30c3

def z526 : W := mkw 0x002006100440b404 0x0002006100440b40 0x79e406303fc0fc0b 0x679e406303fc0fc0

def z527 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x11f807f03c00fc08 0x611f807f03c00fc0

def z528 : W := mkw 0x00df900033000008 0x800df90003300000 0xfbfff8003fc00003 0x1fbfff8003fc0000

def z529 : W := mkw 0x002006000c28a284 0x4002006000c28a28 0x3de006003c3cf3cf 0x23de006003c3cf3c

def z530 : W := mkw 0x0000000008280000 0x4000000000828000 0x010000003c3c0007 0x0010000003c3c000

def z531 : W := mkw 0xc12806503740fc04 0x8c12806503740fc0 0x39e006003fc0fc0b 0x239e006003fc0fc0

def z532 : W := mkw 0x120828107bff1450 0xf120828107bff145 0xed051a33ffff3cff 0xfed051a33ffff3cf

def z533 : W := mkw 0x02ffffafbbbf000f 0xf02ffffafbbbf000 0xfbfffdcc3fff0007 0x1fbfffdcc3fff000

def z534 : W := mkw 0xc1bc07703f68fe86 0xcc1bc07703f68fe8 0x7dfc07f03ffcffcf 0x67dfc07f03ffcffc

def z535 : W := mkw 0x2043f08f80120129 0x02043f08f8012012 0x8603f80fc0330334 0x98603f80fc033033

def z536 : W := mkw 0x009c000033000000 0x8009c00003300000 0x11f800003c000000 0x011f800003c00000

def z537 : W := mkw 0x02f79e0a1dada28c 0x702f79e0a1dada28 0xbde71e0e3dfcf3cf 0xabde71e0e3dfcf3c

def z538 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x59f805c03e00cc09 0x659f805c03e00cc0

def z539 : W := mkw 0x009c080033850000 0xa009c08003385000 0xf9fd18003fcf0007 0x1f9fd18003fcf000

def z540 : W := mkw 0xc1ff97703740fc0e 0x8c1ff97703740fc0 0xfbfffff03fc0fc0b 0x7fbfffff03fc0fc0

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000233c0000000 0xe00000233c000000

def z542 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xbffbe7ce3c3cf3cf 0xabffbe7ce3c3cf3c

def z543 : W := mkw 0x0043000a08280280 0x40043000a0828028 0xac03020e003c33cf 0xaac03020e003c33c

def z544 : W := mkw 0x02dfb8003fbfa288 0xf02dfb8003fbfa28 0xfffff8003ffff3cf 0x1fffff8003ffff3c

def z545 : W := mkw 0x000041a580000003 0x0000041a58000000 0x000001f1c0000000 0x4000001f1c000000

def z546 : W := mkw 0xa02867efa2124927 0x8a02867efa212492 0xde1ae7ffe233cf3d 0xfde1ae7ffe233cf3

def z547 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0xfbfff8003c300000 0x1fbfff8003c30000

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x8400000100030034 0x9840000010003003

def z549 : W := mkw 0x0020060a0400a284 0x00020060a0400a28 0xac01060e000cf3cf 0xaac01060e000cf3c

def z550 : W := mkw 0x1000489540c51451 0x21000489540c5145 0xfe1fffffc3cf3cff 0xffe1fffffc3cf3cf

def z551 : W := mkw 0xa09c60c533124921 0x8a09c60c53312492 0xfffee5cd3ff3cf3f 0xffffee5cd3ff3cf3

def z552 : W := mkw 0x02dfb80033970008 0xb02dfb8003397000 0xfafff80003c30000 0x1fafff80003c3000

def z553 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xac01020203cf3cff 0xaac01020203cf3cf

def z554 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x01e000001c000000 0x001e000001c00000

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000102030c30 0x54000000102030c3

def z556 : W := mkw 0x0063468f00000005 0x00063468f0000000 0xfafbe7cf00000000 0xffafbe7cf0000000

def z557 : W := mkw 0x10630e1a4cedb6d4 0x610630e1a4cedb6d 0xede51a33dfcf3cff 0xfede51a33dfcf3cf

def z558 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x69e402301fc03c0b 0x669e402301fc03c0

def z559 : W := mkw 0x12ffbe1a7fffb6dc 0xf12ffbe1a7fffb6d 0xfffffe3fffffffff 0xffffffe3ffffffff

def z560 : W := mkw 0xc1b407700440fc06 0x0c1b407700440fc0 0x78fc07f00000fc08 0x678fc07f00000fc0

def z561 : W := mkw 0xc1ffd7ffb740fc0f 0x8c1ffd7ffb740fc0 0x7bfee7fc3fc0fc0b 0x67bfee7fc3fc0fc0

def z562 : W := mkw 0x029c28003bbf0000 0xf029c28003bbf000 0x79fc00003fff0007 0x079fc00003fff000

def z563 : W := mkw 0x10200e1a44c5b6d4 0x210200e1a44c5b6d 0xec051e3fc3cfffff 0xfec051e3fc3cffff

def z564 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0xbbfbe0003c3c0007 0x0bbfbe0003c3c000

def z565 : W := mkw 0x10f79f3ac0c5145e 0x210f79f3ac0c5145 0x20e51a32c1cc30c2 0x020e51a32c1cc30c

def z566 : W := mkw 0x0043900a80000008 0x00043900a8000000 0x00011802c0000000 0x000011802c000000

def z567 : W := mkw 0x120828107bff1450 0xf120828107bff145 0x050000003fff3cff 0x0050000003fff3cf

def z568 : W := mkw 0xa06346cf0c28eba5 0x4a06346cf0c28eba 0xbde307cf3c3cffff 0xebde307cf3c3cfff

def z569 : W := mkw 0xa00040c500004921 0x0a00040c50000492 0xcc0005cd0203cf3d 0xfcc0005cd0203cf3

def z570 : W := mkw 0x02ffbe003fbfa00c 0xf02ffbe003fbfa00 0xfbfffe003ffff00f 0x3fbfffe003ffff00

def z571 : W := mkw 0xc3bc2f703ffffc06 0xfc3bc2f703ffffc0 0x79fc07f03ffffc0f 0x679fc07f03ffffc0

def z572 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x24051a32c3cf3cff 0x024051a32c3cf3cf

def z573 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb9e3060e1c0c30c2 0xab9e3060e1c0c30c

def z574 : W := mkw 0xc3ffbf603fbfe80e 0xfc3ffbf603fbfe80 0xfbfffdc03fffc007 0x1fbfffdc03fffc00

def z575 : W := mkw 0x004300000c28a280 0x4004300000c28a28 0xbde300003c3cf3cf 0x0bde300003c3cf3c

def z576 : W := mkw 0x41bc07303740b406 0x841bc07303740b40 0x79fc02303fc03003 0x079fc02303fc0300

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x84010002000c00c4 0x884010002000c00c

def z578 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x84011a33c00f3cfc 0xf84011a33c00f3cf

def z579 : W := mkw 0x1000001040401450 0x0100000104040145 0xac010233c00c3cff 0xeac010233c00c3cf

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc02040d2233cf3d 0xfdc02040d2233cf3

def z581 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xec05180003cf3cff 0x1ec05180003cf3cf

def z582 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x9de2040c3c30c30d 0xa9de2040c3c30c30

def z583 : W := mkw 0xc1ff077a3f68fe86 0xcc1ff077a3f68fe8 0x79fd07f23fccfccb 0x679fd07f23fccfcc

def z584 : W := mkw 0x0008200022120000 0x8000820002212000 0xde1ae00122330c3d 0xfde1ae00122330c3

def z585 : W := mkw 0xc16b065a3f68fe84 0xcc16b065a3f68fe8 0xbde3060e3ffcffcf 0xabde3060e3ffcffc

def z586 : W := mkw 0x109c081073c51450 0xa109c081073c5145 0xfdfd1a33ffcf3cff 0xffdfd1a33ffcf3cf

def z587 : W := mkw 0xa00820402e3aeba0 0xca00820402e3aeba 0x050000003e3fffff 0x0050000003e3ffff

def z588 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x6c04023003cf3cff 0x66c04023003cf3cf

def z589 : W := mkw 0x00b4073000401406 0x000b407300040140 0x78fc07f003c03c0b 0x678fc07f003c03c0

def z590 : W := mkw 0x0063d68f8c28a28d 0x40063d68f8c28a28 0xbfe3fe0ffc3cf3cf 0xbbfe3fe0ffc3cf3c

def z591 : W := mkw 0x1000080040850050 0x2100008004085005 0xcc011803c20f0cfd 0xfcc011803c20f0cf

def z592 : W := mkw 0xa2dff8c53bbf4929 0xfa2dff8c53bbf492 0xfbfff9c13fff0c37 0x5fbfff9c13fff0c3

def z593 : W := mkw 0x0043000008280000 0x4004300000828000 0xbde302023c3c30cf 0xabde302023c3c30c

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000100000000 0xfc80000010000000

def z595 : W := mkw 0xa24bf8c52abf4929 0xfa24bf8c52abf492 0xde1bfdcd223fcf3d 0xfde1bfdcd223fcf3

def z596 : W := mkw 0x00d7980000850008 0x200d798000085000 0xfafff80003cf0007 0x1fafff80003cf000

def z597 : W := mkw 0x02d7b80008bf0008 0x702d7b80008bf000 0xfafff800003f0004 0x1fafff800003f000

def z598 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xdafae5cd00000000 0xfdafae5cd0000000

def z599 : W := mkw 0x00b4072000000006 0x000b407200000000 0xf8fd1ff3c0000000 0xff8fd1ff3c000000

def z600 : W := mkw 0x0043000008280000 0x4004300000828000 0x21e100001c0c0002 0x021e100001c0c000

def z601 : W := mkw 0x0043000a08280280 0x40043000a0828028 0x00010002000c00c0 0x000010002000c00c

def z602 : W := mkw 0x0008200022120000 0x8000820002212000 0x121ae00020300000 0x0121ae0002030000

def z603 : W := mkw 0x8008005022405c00 0x88008005022405c0 0x781c07f023c0fc0b 0x6781c07f023c0fc0

def z604 : W := mkw 0x002006000400a004 0x0002006000400a00 0xbde106023c0cf0cf 0xabde106023c0cf0c

def z605 : W := mkw 0x009c000033000000 0x8009c00003300000 0x401c000003c00000 0x0401c000003c0000

def z606 : W := mkw 0x800840c522004801 0x8800840c52200480 0xda1ae5cd2200cc09 0xfda1ae5cd2200cc0

def z607 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x040005cd2233cf3d 0xe040005cd2233cf3

def z608 : W := mkw 0xc12807703740fc06 0x8c12807703740fc0 0x010007f03fc0fc0b 0x6010007f03fc0fc0

def z609 : W := mkw 0xd1200f7044c5fc56 0x2d1200f7044c5fc5 0xec051ff3c3cffcff 0xfec051ff3c3cffcf

def z610 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x25e1060e1c0cf3ca 0xa25e1060e1c0cf3c

def z611 : W := mkw 0xa00860d522525d21 0x8a00860d522525d2 0xfe1ee7fd23f3ff3f 0xffe1ee7fd23f3ff3

def z612 : W := mkw 0x0243b80a08bf0288 0x70243b80a08bf028 0x8603f80e003f03c4 0x98603f80e003f03c

def z613 : W := mkw 0x00f7072a0c28a286 0x400f7072a0c28a28 0xfdff07fe3c3cf3cf 0xefdff07fe3c3cf3c

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x80011803c0000000 0x980011803c000000

def z615 : W := mkw 0xb00868d562d75d71 0xab00868d562d75d7 0xde1ae5cd23ffffff 0xfde1ae5cd23fffff

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x280002000000300b 0x2280002000000300

def z617 : W := mkw 0xa0fff7efa212492f 0x8a0fff7efa212492 0xfaffffffe030c300 0xffaffffffe030c30

def z618 : W := mkw 0x00bc06003700a004 0x800bc06003700a00 0x79fc06003fc0f00b 0x279fc06003fc0f00

def z619 : W := mkw 0xa0dff0c522124929 0x8a0dff0c52212492 0xfefffdcd2233cf3d 0xffefffdcd2233cf3

def z620 : W := mkw 0x029cb00033120008 0x9029cb0003312000 0x0218e00000000000 0x00218e0000000000

def z621 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0xea1df80003cf0007 0x1ea1df80003cf000

def z622 : W := mkw 0x8008004022004800 0x8800800402200480 0xdc1805c12203cc3d 0xfdc1805c12203cc3

def z623 : W := mkw 0xe10820503752fd20 0x8e10820503752fd2 0x050000003ff3ff3f 0x0050000003ff3ff3

def z624 : W := mkw 0xc1ff076a3f28ea86 0xcc1ff076a3f28ea8 0x11fa05cc3c30c300 0x011fa05cc3c30c30

def z625 : W := mkw 0x0000408500000001 0x0000040850000000 0x000005cd00000000 0xe000005cd0000000

def z626 : W := mkw 0x0000081000c51400 0x20000081000c5140 0xe8051a3003cf3c0f 0x7e8051a3003cf3c0

def z627 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x39e106023c0cf0cb 0x239e106023c0cf0c

def z628 : W := mkw 0x1043081048ed1450 0x61043081048ed145 0xfde71a33ffff3cff 0xffde71a33ffff3cf

def z629 : W := mkw 0x0043000008280000 0x4004300000828000 0xbde3040c3c3cc30f 0xabde3040c3c3cc30

def z630 : W := mkw 0x0043000a08280280 0x40043000a0828028 0x9c03040e203cc3cd 0xa9c03040e203cc3c

def z631 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x79fc01f03fc00c03 0x479fc01f03fc00c0

def z632 : W := mkw 0x02ffbf2abbbf000e 0xf02ffbf2abbbf000 0xfbfffa32ffff0007 0x1fbfffa32ffff000

def z633 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x9e1ae5cc2030c30d 0xa9e1ae5cc2030c30

def z634 : W := mkw 0x0243b80008bf0008 0x70243b80008bf000 0xbbe3f8003c3f0007 0x1bbe3f8003c3f000

def z635 : W := mkw 0xc3dfb8503ffffc08 0xfc3dfb8503ffffc0 0xfbfff8003ffffc0f 0x1fbfff8003ffffc0

def z636 : W := mkw 0x10f7d7bfc040145f 0x010f7d7bfc040145 0xfeffffffc0003cf8 0xffeffffffc0003cf

def z637 : W := mkw 0xe1bc67e53712e927 0x8e1bc67e53712e92 0x13fae5cc3c30c300 0x013fae5cc3c30c30

def z638 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x33fff8003dfc0002 0x033fff8003dfc000

def z639 : W := mkw 0xa00868c522974921 0xaa00868c52297492 0xfe1ffdcd23ffcf3f 0xffe1ffdcd23ffcf3

def z640 : W := mkw 0x802806402600e804 0x8802806402600e80 0x79f807c03e00fc0b 0x679f807c03e00fc0

def z641 : W := mkw 0xa2dff8c53bbf4929 0xfa2dff8c53bbf492 0xfbfffdcc3fffc307 0x1fbfffdcc3fffc30

def z642 : W := mkw 0xc10000500440fc00 0x0c10000500440fc0 0x000000000000fc08 0x0000000000000fc0

def z643 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x581c05f023c0cc09 0x6581c05f023c0cc0

def z644 : W := mkw 0xc3ffb7603f3ae80e 0xdc3ffb7603f3ae80 0x13fae5c03c30c000 0x013fae5c03c30c00

def z645 : W := mkw 0xb00040d540405d71 0x0b00040d540405d7 0x040007ffc000fff8 0xe040007ffc000fff

def z646 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xda1ae5cd02030c30 0xfda1ae5cd02030c3

def z647 : W := mkw 0xc1bc077033405c06 0x8c1bc077033405c0 0x78fc07f003c00c00 0x678fc07f003c00c0

def z648 : W := mkw 0x0000000a00000280 0x00000000a0000028 0x0400000e000003c0 0x80400000e000003c

def z649 : W := mkw 0x410000101540b400 0x0410000101540b40 0x010000001dc03002 0x0010000001dc0300

def z650 : W := mkw 0x41f7d7bf9540b40f 0x041f7d7bf9540b40 0xfbffffffddc03002 0xffbffffffddc0300

def z651 : W := mkw 0x1043d88fc0850059 0x21043d88fc085005 0x8603f80fc00f00f4 0x98603f80fc00f00f

def z652 : W := mkw 0x1000080040850050 0x2100008004085005 0x00011802c00c00c0 0x000011802c00c00c

def z653 : W := mkw 0xc3ffffffbffffc0f 0xfc3ffffffbffffc0 0xfbfffffffffffc0f 0xffbfffffffffffc0

def z654 : W := mkw 0xa2dff0c53b3a4929 0xda2dff0c53b3a492 0xdffae5cd3e33cf3d 0xfdffae5cd3e33cf3

def z655 : W := mkw 0x1243b80048bf0058 0x71243b80048bf005 0x8603f803c03f00f4 0x98603f803c03f00f

def z656 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb9e3060e3c30c300 0xab9e3060e3c30c30

def z657 : W := mkw 0x02dff8853bbf0009 0xf02dff8853bbf000 0xfbfffdcd3fff0007 0xffbfffdcd3fff000

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000202000030c8 0xa04000202000030c

def z659 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x5a18e5c12203cc39 0x75a18e5c12203cc3

def z660 : W := mkw 0x1000001040401450 0x0100000104040145 0xcc000233c2033cfd 0xfcc000233c2033cf

def z661 : W := mkw 0x0008000033000000 0x8000800003300000 0x010000003fc00003 0x0010000003fc0000

def z662 : W := mkw 0x0008000022000000 0x8000800002200000 0x5818000022000001 0x0581800002200000

def z663 : W := mkw 0x0000080000850000 0x2000008000085000 0xec05180103cf0c3f 0xfec05180103cf0c3

def z664 : W := mkw 0x0000080000850000 0x2000008000085000 0x4004180003c30000 0x14004180003c3000

def z665 : W := mkw 0x000000000c28a280 0x4000000000c28a28 0x010000003c30c300 0x0010000003c30c30

def z666 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x39e406303dc0f00b 0x239e406303dc0f00

def z667 : W := mkw 0xa20868c53bbf4921 0xfa20868c53bbf492 0xdf1ae5cd3fffcf3f 0xfdf1ae5cd3fffcf3

def z668 : W := mkw 0x12d7981059ed1458 0x712d7981059ed145 0xede51a33dfcf3cff 0xfede51a33dfcf3cf

def z669 : W := mkw 0x0020060a0400a284 0x00020060a0400a28 0x3de0060e3c00f3cb 0xa3de0060e3c00f3c

def z670 : W := mkw 0x0063060a00000004 0x00063060a0000000 0x20e1020200000000 0x020e102020000000

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0xec051a33c2030c3d 0xfec051a33c2030c3

def z672 : W := mkw 0x0094000011000000 0x0009400001100000 0x21e400001dc00002 0x021e400001dc0000

def z673 : W := mkw 0xc1ffd7efb700e80f 0x8c1ffd7efb700e80 0xfbfffffffc00c000 0xffbfffffffc00c00

def z674 : W := mkw 0xd12007704440fc56 0x0d12007704440fc5 0x040007f3c000fcf8 0xe040007f3c000fcf

def z675 : W := mkw 0x10630e1a40c51454 0x210630e1a40c5145 0xfce71e3fc3cf3cff 0xffce71e3fc3cf3cf

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8010000000c0007 0x0a8010000000c000

def z677 : W := mkw 0x02ffb60a3f3aa28c 0xd02ffb60a3f3aa28 0xbffbe60e3c3cf3cf 0xabffbe60e3c3cf3c

def z678 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0xdbfae0003e330005 0x1dbfae0003e33000

def z679 : W := mkw 0x02ffbe0a3fbfa28c 0xf02ffbe0a3fbfa28 0xfbfffa023fff30c7 0x1fbfffa023fff30c

def z680 : W := mkw 0x1043081a48ed16d0 0x61043081a48ed16d 0xec071a3fc3ff3fff 0xfec071a3fc3ff3ff

def z681 : W := mkw 0x00b4072000000006 0x000b407200000000 0x10f805c000000000 0x010f805c00000000

def z682 : W := mkw 0xd1bc0f7077c5fc56 0xad1bc0f7077c5fc5 0x7dfc07f03fcffcff 0x67dfc07f03fcffcf

def z683 : W := mkw 0x024b28003bbf0000 0xf024b28003bbf000 0xb9e300003fff0007 0x0b9e300003fff000

def z684 : W := mkw 0x0043d08f80000009 0x00043d08f8000000 0x0202e00c00000000 0x00202e00c0000000

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400040c0000c308 0xa0400040c0000c30

def z686 : W := mkw 0x0200b80000970008 0x30200b8000097000 0x0200f80000030000 0x10200f8000003000

def z687 : W := mkw 0x1000080040850050 0x2100008004085005 0xac011a03c00f30ff 0xbac011a03c00f30f

def z688 : W := mkw 0xc3ffb7703f7afc0e 0xdc3ffb7703f7afc0 0x7bfee7f03ff0fc0b 0x67bfee7f03ff0fc0

def z689 : W := mkw 0x2000408500000121 0x0200040850000012 0x0400000d00000330 0x80400000d0000033

def z690 : W := mkw 0xc3dfb9703bff5c0a 0xfc3dfb9703bff5c0 0xfbfff9f03fff0c07 0x5fbfff9f03fff0c0

def z691 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x79fc07f03c00c000 0x679fc07f03c00c00

def z692 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe8051831c3cf0c37 0x5e8051831c3cf0c3

def z693 : W := mkw 0xc19c016033004802 0x8c19c01603300480 0x001801c000000000 0x0001801c00000000

def z694 : W := mkw 0x02ffb60a3f3aa28c 0xd02ffb60a3f3aa28 0x13fae40c3c30c300 0x013fae40c3c30c30

def z695 : W := mkw 0x2000608500120121 0x0200060850012012 0x0200e00100030030 0x10200e0010003003

def z696 : W := mkw 0xe3fffff53ffffd2f 0xfe3fffff53ffffd2 0xfffffffd3fffff3f 0xffffffffd3fffff3

def z697 : W := mkw 0xc30828503ffffc00 0xfc30828503ffffc0 0x010000003ffffc0f 0x0010000003ffffc0

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x180004002000c009 0x2180004002000c00

def z699 : W := mkw 0xb00868d562d75d71 0xab00868d562d75d7 0xee1dfbf3c3cf3cff 0xfee1dfbf3c3cf3cf

def z700 : W := mkw 0x02d7900019280008 0x502d790001928000 0x01e000001c000000 0x001e000001c00000

def z701 : W := mkw 0x00f797200000000e 0x000f797200000000 0xfafffff000000000 0x7fafffff00000000

def z702 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0xe9e518001fcf0007 0x1e9e518001fcf000

def z703 : W := mkw 0xa2fffecf3fbfebad 0xfa2fffecf3fbfeba 0xffffffcf3fffffff 0xfffffffcf3ffffff

def z704 : W := mkw 0xa008204022124920 0x8a00820402212492 0x000000002030c300 0x0000000002030c30

def z705 : W := mkw 0xc12007600400e806 0x0c12007600400e80 0x000005c00000c000 0x0000005c00000c00

def z706 : W := mkw 0x10f7dfbfc0c5145f 0x210f7dfbfc0c5145 0xfaffffffc1cc30c2 0xffaffffffc1cc30c

def z707 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1ae7ffe233cf3d 0xfde1ae7ffe233cf3

def z708 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1ee7fd2233cf3d 0xffe1ee7fd2233cf3

def z709 : W := mkw 0x0094d1a58c28a28b 0x40094d1a58c28a28 0x471cf9f1fc3cf3cf 0x5471cf9f1fc3cf3c

def z710 : W := mkw 0x00b4d7a58400a00f 0x000b4d7a58400a00 0x7bfcfff1fc00f00b 0x77bfcfff1fc00f00

def z711 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xb2ffffffc0000000 0x9b2ffffffc000000

def z712 : W := mkw 0xc1bc27703752fc06 0x8c1bc27703752fc0 0xfffee7fc3ff3ff0f 0xffffee7fc3ff3ff0

def z713 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffe0300005 0xffaffffffe030000

def z714 : W := mkw 0x12dfb0107b7a1458 0xd12dfb0107b7a145 0x17fae233fc303cf8 0xe17fae233fc303cf

def z715 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xda1ef9f1c0000000 0x5da1ef9f1c000000

def z716 : W := mkw 0xe1bc07703740fd26 0x8e1bc07703740fd2 0x7dfc07f03fc0ff3b 0x67dfc07f03fc0ff3

def z717 : W := mkw 0x0063072a0c28a286 0x40063072a0c28a28 0xbde307fe3c3cf3cf 0xebde307fe3c3cf3c

def z718 : W := mkw 0xa00060c500124921 0x0a00060c50012492 0xde1ae5cd0033cf3c 0xfde1ae5cd0033cf3

def z719 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8003dfc0002 0x1fbfff8003dfc000

def z720 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x72ffffffc0000000 0x572ffffffc000000

def z721 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffc003fffc00f 0x3fbfffc003fffc00

def z722 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1ffdcd2233cf3d 0xffe1ffdcd2233cf3

def z723 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1bfdcfe233cf3d 0xfde1bfdcfe233cf3

def z724 : W := mkw 0x61b467b51552b527 0x061b467b51552b52 0xa7e6e23d1df33336 0x9a7e6e23d1df3333

def z725 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbfffffffc3cf3c2 0xffbfffffffc3cf3c

def z726 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbfffffffc30f30b 0xffbfffffffc30f30

def z727 : W := mkw 0x10630e1a4cedb6d4 0x610630e1a4cedb6d 0x51e61c3dfff3cf30 0x551e61c3dfff3cf3

def z728 : W := mkw 0x0243f88508bf0009 0x70243f88508bf000 0x8203f80d003f0004 0x98203f80d003f000

def z729 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x421cfbf3c0000000 0xf421cfbf3c000000

def z730 : W := mkw 0xb00868d562d75d71 0xab00868d562d75d7 0x321ffffee1fcf3c2 0x0321ffffee1fcf3c

def z731 : W := mkw 0x02d7b80019bf0008 0x702d7b80019bf000 0x23e7f8001dfc0002 0x023e7f8001dfc000

def z732 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfc071a33e3ff3cff 0xffc071a33e3ff3cf

def z733 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xd61ae5cd2233cf34 0xdd61ae5cd2233cf3

def z734 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde3063ffc3cf3cf 0xebde3063ffc3cf3c

def z735 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fd1ff03fc0fc0b 0x7f9fd1ff03fc0fc0

def z736 : W := mkw 0xa0ffb76aa212492e 0x8a0ffb76aa212492 0x24e51a32e233cf3d 0x024e51a32e233cf3

def z737 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x23fdf8001dcc0002 0x023fdf8001dcc000

def z738 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x121ae5cc2233cf30 0x0121ae5cc2233cf3

def z739 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffdc03fff0007 0x7fbfffdc03fff000

def z740 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1be5cf223fcffd 0xfde1be5cf223fcff

def z741 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8013fff0037 0x9fffff8013fff003

def z742 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8003fffc30f 0x1fffff8003fffc30

def z743 : W := mkw 0xc12806503740fc04 0x8c12806503740fc0 0x79f807c03fc0fc0b 0x679f807c03fc0fc0

def z744 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfbfee7f03fc0fc0b 0x7fbfee7f03fc0fc0

def z745 : W := mkw 0xc363bf700cfffc0e 0x7c363bf700cfffc0 0x8203fff0003ffc0c 0x78203fff0003ffc0

def z746 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1ae7cf2233fffd 0xfde1ae7cf2233fff

def z747 : W := mkw 0xc1df017a3b685e82 0xcc1df017a3b685e8 0xc41f01fe03fc0fc4 0xcc41f01fe03fc0fc

def z748 : W := mkw 0x00b4d7af8000000f 0x000b4d7af8000000 0x421cfdfdc0000000 0x5421cfdfdc000000

def z749 : W := mkw 0x809c005033405c00 0x8809c005033405c0 0x79fc07f03fc0fc0b 0x679fc07f03fc0fc0

def z750 : W := mkw 0xc1bc077a3740fc06 0x8c1bc077a3740fc0 0x79fc07fe3fc0fc0b 0xe79fc07fe3fc0fc0

def z751 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe8051a33c3cf3cf7 0x5e8051a33c3cf3cf

def z752 : W := mkw 0xa2dfb8403bbf4928 0xfa2dfb8403bbf492 0xfffff8013fffcf3f 0xffffff8013fffcf3

def z753 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffa33ffff30cf 0xffffffa33ffff30c

def z754 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x5e1ae5cc2233cf3d 0x65e1ae5cc2233cf3

def z755 : W := mkw 0xd1bc0f607785e856 0xad1bc0f607785e85 0x95f91dc3fc0fc0f4 0x995f91dc3fc0fc0f

def z756 : W := mkw 0x00d7d1af8828028b 0x400d7d1af8828028 0xc61ff9ffc03c03c4 0xdc61ff9ffc03c03c

def z757 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffe000c009 0xffaffffffe000c00

def z758 : W := mkw 0x02286fafbbbf0007 0xf02286fafbbbf000 0x010007ffffff0007 0xe010007ffffff000

def z759 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xee1dfbf3c00c30cf 0xfee1dfbf3c00c30c

def z760 : W := mkw 0x02dfb9203bbf000a 0xf02dfb9203bbf000 0xfbfff9f03fff0007 0x5fbfff9f03fff000

def z761 : W := mkw 0xc1bc27703752fc06 0x8c1bc27703752fc0 0x7bfce7f03fc3fc0b 0x77bfce7f03fc3fc0

def z762 : W := mkw 0x024b28003bbf0000 0xf024b28003bbf000 0xfbfbe0003fff0007 0x1fbfbe0003fff000

def z763 : W := mkw 0x82dfb8403bbf4808 0xf82dfb8403bbf480 0xfbfff9c03fff0c07 0x5fbfff9c03fff0c0

def z764 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fd1ff2ffc0fc0b 0x679fd1ff2ffc0fc0

def z765 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde7063e3c3cf3cf 0xefde7063e3c3cf3c

def z766 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfd1ff3ffccfccf 0xffdfd1ff3ffccfcc

def z767 : W := mkw 0xa06b66cf2e3aeba5 0xca06b66cf2e3aeba 0x63f9e3c31e0f3cf2 0x563f9e3c31e0f3cf

def z768 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde3060e3e3fffff 0xabde3060e3e3ffff

def z769 : W := mkw 0x00f7d7af8400a28f 0x000f7d7af8400a28 0xfeffffffc00cf3cf 0xffeffffffc00cf3c

def z770 : W := mkw 0x0063468f00000005 0x00063468f0000000 0xfaffffffc0000000 0xffaffffffc000000

def z771 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8013fff0c37 0x5fbfff8013fff0c3

def z772 : W := mkw 0x00df20003b3a0000 0xc00df20003b3a000 0xfbffe0003fff0007 0x1fbffe0003fff000

def z773 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x9e1ae5cc2233cf3d 0xa9e1ae5cc2233cf3

def z774 : W := mkw 0x00d7d1a58828000b 0x400d7d1a58828000 0xfbfff9f1fc3c0007 0x5fbfff9f1fc3c000

def z775 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x51fc07f03fc0fc08 0x651fc07f03fc0fc0

def z776 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x61fc03f01dc03002 0x461fc03f01dc0300

def z777 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x7bfee0003fff0007 0x07bfee0003fff000

def z778 : W := mkw 0x00d7d1af8000000b 0x000d7d1af8000000 0x421df9f3c0000000 0x5421df9f3c000000

def z779 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfbfff801ffff0037 0x1fbfff801ffff003

def z780 : W := mkw 0x412047bf8440b407 0x0412047bf8440b40 0x000007ffc0003000 0xe000007ffc000300

def z781 : W := mkw 0x00f7d7af8828028f 0x400f7d7af8828028 0xfffffffffc3c03c7 0xffffffffffc3c03c

def z782 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x621dfbf3c0000000 0x5621dfbf3c000000

def z783 : W := mkw 0xe12047f50440fd27 0x0e12047f50440fd2 0x000007f10000fc38 0x6000007f10000fc3

def z784 : W := mkw 0xc12047ff8440fe87 0x0c12047ff8440fe8 0x040007ffc000ffc8 0xe040007ffc000ffc

def z785 : W := mkw 0x00b4d7af8000000f 0x000b4d7af8000000 0xda1effffc0000000 0xfda1effffc000000

def z786 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x79fc07f03dc0f00b 0x679fc07f03dc0f00

def z787 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x31fc07f03dc0fc0a 0x631fc07f03dc0fc0

def z788 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1ee5cd23f3cf3f 0xffe1ee5cd23f3cf3

def z789 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x53fef8003fff0007 0x153fef8003fff000

def z790 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x7dfc07f13fc0fc3b 0xe7dfc07f13fc0fc3

def z791 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x7afefffdc0000000 0x77afefffdc000000

def z792 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc0300304 0xffeffffffc030030

def z793 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x68051a33c3cf3cfb 0x768051a33c3cf3cf

def z794 : W := mkw 0xb008285062d75d70 0xab008285062d75d7 0x0000000003c30c30 0x00000000003c30c3

def z795 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffa32ffff0007 0x1fbfffa32ffff000

def z796 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffa33ffff0c3f 0xffffffa33ffff0c3

def z797 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfffffffffc30f3c8 0xffffffffffc30f3c

def z798 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x32ffffffc0000000 0xe32ffffffc000000

def z799 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x13fae0003ff30000 0x013fae0003ff3000

def z800 : W := mkw 0x00f7d7af8400a28f 0x000f7d7af8400a28 0xfaffffffc000c300 0xffaffffffc000c30

def z801 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfbfff802ffff00c7 0x1fbfff802ffff00c

def z802 : W := mkw 0xd1bc077a7740fed6 0x8d1bc077a7740fed 0x7dfc07ffffc0fffb 0xe7dfc07ffffc0fff

def z803 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x51fc01f03fc00c00 0x451fc01f03fc00c0

def z804 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0xfbfff8003dfc0007 0x1fbfff8003dfc000

def z805 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x33fff8003fff0007 0x033fff8003fff000

def z806 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x31fc07f03fc0fc0b 0x031fc07f03fc0fc0

def z807 : W := mkw 0x1000489540c51451 0x21000489540c5145 0xde1ae5cd03cf3cff 0xfde1ae5cd03cf3cf

def z808 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0x63fdf8001dcc0002 0x163fdf8001dcc000

def z809 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfe07fd3ff3ff3f 0xffdfe07fd3ff3ff3

def z810 : W := mkw 0x009c000033000000 0x8009c00003300000 0xfbfee0003fc00003 0x1fbfee0003fc0000

def z811 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8003ff30000 0x1fbfff8003ff3000

def z812 : W := mkw 0x00f7d7a58000000f 0x000f7d7a58000000 0xfafffff1c0000000 0x7fafffff1c000000

def z813 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x7dfc07f23fc0fccb 0xe7dfc07f23fc0fcc

def z814 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffe03cf3cf 0xffeffffffe03cf3c

def z815 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x43fcf8001fc30000 0x143fcf8001fc3000

def z816 : W := mkw 0x82dfb8403bbf4808 0xf82dfb8403bbf480 0xfffffdc13fffcc3f 0xffffffdc13fffcc3

def z817 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x31fc07f01dc03002 0x031fc07f01dc0300

def z818 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0xfbfff8001fcf0007 0x1fbfff8001fcf000

def z819 : W := mkw 0xc12047ff8440fc07 0x0c12047ff8440fc0 0x000007fc0000fc08 0x6000007fc0000fc0

def z820 : W := mkw 0x00f7d7af8400a00f 0x000f7d7af8400a00 0xfffffffffc30f30f 0xffffffffffc30f30

def z821 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fd07f23fc0fc0b 0xef9fd07f23fc0fc0

def z822 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xeafdfbf3c0000000 0xfeafdfbf3c000000

def z823 : W := mkw 0x0043000008280000 0x4004300000828000 0xbde3060e3c3cf3cf 0xabde3060e3c3cf3c

def z824 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0xfbfff8003ff00003 0x1fbfff8003ff0000

def z825 : W := mkw 0x0000408500000001 0x0000040850000000 0x421cf9f1c0000000 0x5421cf9f1c000000

def z826 : W := mkw 0x02dfb920bbbf000a 0xf02dfb920bbbf000 0xfbfff830ffff0007 0x1fbfff830ffff000

def z827 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x3de2060c3c3cf3cf 0x23de2060c3c3cf3c

def z828 : W := mkw 0x029c28003bbf0000 0xf029c28003bbf000 0xfbfee0003fff0007 0x1fbfee0003fff000

def z829 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x51fc05f03fc0fc0b 0x451fc05f03fc0fc0

def z830 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfffffffffe3fffff 0xffffffffffe3ffff

def z831 : W := mkw 0x024bb8003bbf0008 0xf024bb8003bbf000 0xbbe3f8003fff0007 0x1bbe3f8003fff000

def z832 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f03dc0f002 0x679fc07f03dc0f00

def z833 : W := mkw 0x00b4072011000006 0x000b407201100000 0x79fc07f01dc00002 0x679fc07f01dc0000

def z834 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc000c308 0xffeffffffc000c30

def z835 : W := mkw 0x0243b80008bf0008 0x70243b80008bf000 0xfbe7f8003fff0007 0x1fbe7f8003fff000

def z836 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xbbfff8003dfc0007 0x0bbfff8003dfc000

def z837 : W := mkw 0xc14bd0dfb740fc09 0x8c14bd0dfb740fc0 0x8303f80fffc0fc0b 0x98303f80fffc0fc0

def z838 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xde1efdfde030c30d 0xfde1efdfde030c30

def z839 : W := mkw 0x02dfb80a3bbf0288 0xf02dfb80a3bbf028 0xfbfff8023fff00c7 0x1fbfff8023fff00c

def z840 : W := mkw 0x824bb8402abf4808 0xf824bb8402abf480 0xda1bfdc0223fcc0d 0x7da1bfdc0223fcc0

def z841 : W := mkw 0x00d7d1a58000000b 0x000d7d1a58000000 0xfafffdfdc0000000 0xffafffdfdc000000

def z842 : W := mkw 0xc3bcb7703752fc0e 0x9c3bcb7703752fc0 0x7bfce7f03fc0fc0b 0x67bfce7f03fc0fc0

def z843 : W := mkw 0x10f7dfbfc0c5145f 0x210f7dfbfc0c5145 0x16fae5cc03cf3cff 0x016fae5cc03cf3cf

def z844 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x5a1ae5cd2233cf39 0x75a1ae5cd2233cf3

def z845 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xec071a3fc3ff3fff 0xfec071a3fc3ff3ff

def z846 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xca1cf9f1c0000000 0xfca1cf9f1c000000

def z847 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f03fc0cc00 0x679fc07f03fc0cc0

def z848 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffe030c300 0xffaffffffe030c30

def z849 : W := mkw 0x002006000400a004 0x0002006000400a00 0xbde3060e3c3cf3cf 0xabde3060e3c3cf3c

def z850 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc1ff1ffc0fc0b 0x779fc1ff1ffc0fc0

def z851 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x62fdffffc0000000 0xf62fdffffc000000

def z852 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfdfb07ce3c3cf3cf 0xefdfb07ce3c3cf3c

def z853 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f03fc0f003 0x079fc07f03fc0f00

def z854 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x6a1cfbf1c0000000 0x76a1cfbf1c000000

def z855 : W := mkw 0xb008285062d75d70 0xab008285062d75d7 0xbc03060e23ffffff 0xabc03060e23fffff

def z856 : W := mkw 0x00d7900011000008 0x000d790001100000 0xfbfff8001dc00002 0x1fbfff8001dc0000

def z857 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0x53fefdfdfc30c300 0x553fefdfdfc30c30

def z858 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x7bfdf8003fcf0003 0x17bfdf8003fcf000

def z859 : W := mkw 0xc1bc97703740fc0e 0x8c1bc97703740fc0 0x7bfcfff03fc0fc0b 0x77bfcfff03fc0fc0

def z860 : W := mkw 0x80bc06403700e804 0x880bc06403700e80 0x79fc07c03fc0fc0b 0x679fc07c03fc0fc0

def z861 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x69fc03f01fc03c0b 0x669fc03f01fc03c0

def z862 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f13fc3fc3b 0x779fc07f13fc3fc3

def z863 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xb3fff8003dff0006 0x1b3fff8003dff000

def z864 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xd2fffdffc0000000 0xdd2fffdffc000000

def z865 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc05c03fc0fc0b 0x079fc05c03fc0fc0

def z866 : W := mkw 0xe1bc27703752fd26 0x8e1bc27703752fd2 0xfdfc07f13ff3ff3f 0xffdfc07f13ff3ff3

def z867 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc00030c8 0xffeffffffc00030c

def z868 : W := mkw 0x0000408500000001 0x0000040850000000 0xda1efdfdc0000000 0xfda1efdfdc000000

def z869 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb9e3060e3c3cf3c2 0xab9e3060e3c3cf3c

def z870 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8003fff0c0f 0x7fbfff8003fff0c0

def z871 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0xfbfdf8003fcf0007 0x1fbfdf8003fcf000

def z872 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfeffffffc03cf3cc 0xffeffffffc03cf3c

def z873 : W := mkw 0xf12047f54440fd77 0x0f12047f54440fd7 0x040007ffc000fff8 0xe040007ffc000fff

def z874 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1ae7cd2233ff3f 0xffe1ae7cd2233ff3

def z875 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffe233cf3d 0xffeffffffe233cf3

def z876 : W := mkw 0x00b4d7af8000000f 0x000b4d7af8000000 0x421cfbf3c0000000 0x5421cfbf3c000000

def z877 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc00c30c2 0xffaffffffc00c30c

def z878 : W := mkw 0xa09c40c533004921 0x8a09c40c53300492 0x7dfc05cd3fc0cf3b 0xe7dfc05cd3fc0cf3

def z879 : W := mkw 0x00f7d7af8400a00f 0x000f7d7af8400a00 0xfbffffffdc003002 0xffbffffffdc00300

def z880 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0x33fff8001dcc0002 0x033fff8001dcc000

def z881 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x961ae5cd2033cf3c 0xf961ae5cd2033cf3

def z882 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8001fcf0002 0x1fbfff8001fcf000

def z883 : W := mkw 0xc1b407701540fc06 0x0c1b407701540fc0 0x21e403f01dc03c02 0x421e403f01dc03c0

def z884 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0xfdfd07f3ffccfcff 0xefdfd07f3ffccfcf

def z885 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x25e1060e3c3cf3cf 0xa25e1060e3c3cf3c

def z886 : W := mkw 0xe12047ff8440fd27 0x0e12047ff8440fd2 0x040007ffc000ff38 0xe040007ffc000ff3

def z887 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffa023fff30c7 0x1fbfffa023fff30c

def z888 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x21fc03f01dc03002 0x021fc03f01dc0300

def z889 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffa033fff3cff 0xffffffa033fff3cf

def z890 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x521efdfdc0000000 0x5521efdfdc000000

def z891 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xdbfae0003fff0007 0x1dbfae0003fff000

def z892 : W := mkw 0x00dfb00033120008 0x800dfb0003312000 0xfbfff8003ff30007 0x1fbfff8003ff3000

def z893 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f01fc03c02 0x679fc07f01fc03c0

def z894 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde3060e3e3ff3cf 0xbfde3060e3e3ff3c

def z895 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc20f3cff 0xffeffffffc20f3cf

def z896 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfffffa33ffff00f7 0xffffffa33ffff00f

def z897 : W := mkw 0x0094d1af8000000b 0x00094d1af8000000 0x421cf9ffc0000000 0xd421cf9ffc000000

def z898 : W := mkw 0xb00828506efffff0 0xeb00828506efffff 0x050000003fffffff 0x0050000003ffffff

def z899 : W := mkw 0x00d7d1af8000000b 0x000d7d1af8000000 0xea1ffbffc0000000 0xfea1ffbffc000000

def z900 : W := mkw 0x209c608533120121 0x8209c60853312012 0xfffee00d3ff30337 0x9fffee00d3ff3033

def z901 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x7dfc07f03fccfccf 0x67dfc07f03fccfcc

def z902 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xbbfbe0003fff0007 0x0bbfbe0003fff000

def z903 : W := mkw 0x82dfb8403bbf4808 0xf82dfb8403bbf480 0xfbfff8003fffcc0f 0x1fbfff8003fffcc0

def z904 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8003fff30cf 0x1fffff8003fff30c

def z905 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc05f03fc0cc03 0x479fc05f03fc0cc0

def z906 : W := mkw 0x0063960a0c28a28c 0x40063960a0c28a28 0xbfe3fe0e3c3cf3cf 0xbbfe3fe0e3c3cf3c

def z907 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff8013fff0007 0xffbfff8013fff000

def z908 : W := mkw 0x22dfb8003bbf0128 0xf22dfb8003bbf012 0xfffff8003fff0337 0x1fffff8003fff033

def z909 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xbffffffefc3cf3cf 0xabffffffefc3cf3c

def z910 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbfffffffc3cc307 0xffbfffffffc3cc30

def z911 : W := mkw 0x00f7972a8000000e 0x000f7972a8000000 0xfafffff2c0000000 0x7fafffff2c000000

def z912 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x561ae5cd2233cf3d 0x5561ae5cd2233cf3

def z913 : W := mkw 0xa2dfb8403bbf4928 0xfa2dfb8403bbf492 0xfffffc0c3fffcf3f 0xbfffffc0c3fffcf3

def z914 : W := mkw 0x009c900033000008 0x8009c90003300000 0x7bfcf8003fc00003 0x17bfcf8003fc0000

def z915 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xdbfef8003ff30005 0x1dbfef8003ff3000

def z916 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x93fbf8003fff0007 0x193fbf8003fff000

def z917 : W := mkw 0xd12047ffc440fc57 0x0d12047ffc440fc5 0x040007ffc000fcf8 0xe040007ffc000fcf

def z918 : W := mkw 0x00f7d7af8400a28f 0x000f7d7af8400a28 0xfeffffffe030f3cd 0xffeffffffe030f3c

def z919 : W := mkw 0x02d7b80019bf0008 0x702d7b80019bf000 0x23e5f8001dcf0002 0x123e5f8001dcf000

def z920 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xa3e7f8003fff0007 0x1a3e7f8003fff000

def z921 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0xfdfc07f3ffc3fcff 0xffdfc07f3ffc3fcf

def z922 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xc21df9f3c0000000 0xdc21df9f3c000000

def z923 : W := mkw 0x3243f88548bf0179 0x73243f88548bf017 0x8603f80fc03f03f4 0x98603f80fc03f03f

def z924 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fe07fc3fc0fc0b 0xef9fe07fc3fc0fc0

def z925 : W := mkw 0x00d7d1a58000000b 0x000d7d1a58000000 0x62fdf9f1c0000000 0x562fdf9f1c000000

def z926 : W := mkw 0xe1bc27703752fd26 0x8e1bc27703752fd2 0x79fc07f03fc3fc3b 0x679fc07f03fc3fc3

def z927 : W := mkw 0xa2dfb8403bbf4928 0xfa2dfb8403bbf492 0xfbfff8003fff0c37 0x1fbfff8003fff0c3

def z928 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fe07f03ff0fc0f 0x6f9fe07f03ff0fc0

def z929 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc2030c30 0xffaffffffc2030c3

def z930 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1efdfde233cf3d 0xfde1efdfde233cf3

def z931 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xdafefdfdc0000000 0xfdafefdfdc000000

def z932 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x961ae5cd2233cf3d 0x9961ae5cd2233cf3

def z933 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfafffffec0000000 0x1fafffffec000000

def z934 : W := mkw 0x02df98003bad0008 0xf02df98003bad000 0xfbfff8003fcc0003 0x1fbfff8003fcc000

def z935 : W := mkw 0x00b4d7a58000000f 0x000b4d7a58000000 0xfafefffdc0000000 0xffafefffdc000000

def z936 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc000300b 0xffaffffffc000300

def z937 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0xfbfee0003ff30007 0x1fbfee0003ff3000

def z938 : W := mkw 0x102047bfc440b6d7 0x0102047bfc440b6d 0x040007ffc000fff8 0xe040007ffc000fff

def z939 : W := mkw 0xc1bc27703752fc06 0x8c1bc27703752fc0 0x79fc07f03ff3fc0f 0x679fc07f03ff3fc0

def z940 : W := mkw 0xe1bc27703752fd26 0x8e1bc27703752fd2 0xfffee7f03ff3ff3f 0x7fffee7f03ff3ff3

def z941 : W := mkw 0x00f7d7af8828000f 0x400f7d7af8828000 0xfffffffffc3cc30f 0xffffffffffc3cc30

def z942 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fe07fc3ff0ff0b 0x679fe07fc3ff0ff0

def z943 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x13fae0003dfc0002 0x013fae0003dfc000

def z944 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffc0c3fff0007 0xbfbfffc0c3fff000

def z945 : W := mkw 0xc1bc9770b740fc0e 0x8c1bc9770b740fc0 0x79fc1ff0ffc0fc0b 0x679fc1ff0ffc0fc0

def z946 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x11f807f03fc0fc0b 0x611f807f03fc0fc0

def z947 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x021cf9f0c0000000 0x0021cf9f0c000000

def z948 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x21e407f03fc0fc0b 0x621e407f03fc0fc0

def z949 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x11f805c03fc0cc00 0x011f805c03fc0cc0

def z950 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x79fc05f03fc0cc0b 0x679fc05f03fc0cc0

def z951 : W := mkw 0x1043d88fc8ad02d9 0x61043d88fc8ad02d 0x8603f80fc03f03f4 0x98603f80fc03f03f

def z952 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x561ae5cd2233cf38 0xf561ae5cd2233cf3

def z953 : W := mkw 0x2243f88f88bf0129 0x72243f88f88bf012 0x8603f80fc03f0334 0x98603f80fc03f033

def z954 : W := mkw 0xa2dfb8403bbf4928 0xfa2dfb8403bbf492 0xfbfff8003fffc307 0x1fbfff8003fffc30

def z955 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfc1d1ff3c3cf3cff 0xffc1d1ff3c3cf3cf

def z956 : W := mkw 0x00d7980008ad0008 0x600d7980008ad000 0xfbfff8003fff0007 0x1fbfff8003fff000

def z957 : W := mkw 0xc19c01703740fc02 0x8c19c01703740fc0 0x79fc01f03fc0fc0b 0x479fc01f03fc0fc0

def z958 : W := mkw 0x00d7d1a58000000b 0x000d7d1a58000000 0xfafffbf3c0000000 0xffafffbf3c000000

def z959 : W := mkw 0xe12047ff0440ffa7 0x0e12047ff0440ffa 0x040007ff0000fff8 0xe040007ff0000fff

def z960 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc2030005 0xffaffffffc203000

def z961 : W := mkw 0xc12807703740fc06 0x8c12807703740fc0 0x39e007f03fc0fc0b 0x639e007f03fc0fc0

def z962 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde3060f3c3cffff 0xebde3060f3c3cfff

def z963 : W := mkw 0xc1bc077a3740fe86 0x8c1bc077a3740fe8 0x79fc07fc3fc0ff0b 0x679fc07fc3fc0ff0

def z964 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1ae5cc2233cf3d 0x1de1ae5cc2233cf3

def z965 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x39e3060e3c3cf3cb 0x239e3060e3c3cf3c

def z966 : W := mkw 0xc12047f58440fc07 0x0c12047f58440fc0 0x000007f1c000fc08 0x6000007f1c000fc0

def z967 : W := mkw 0x00f7d7af8400a28f 0x000f7d7af8400a28 0xfaffffffc00030c0 0xffaffffffc00030c

def z968 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff80c3fff0307 0x9fffff80c3fff030

def z969 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x13fef8003df00000 0x013fef8003df0000

def z970 : W := mkw 0xc19c00503740fc00 0x8c19c00503740fc0 0x79fc05c03fc0fc0b 0x679fc05c03fc0fc0

def z971 : W := mkw 0x00f7d7af8828000f 0x400f7d7af8828000 0xfffffffffc3c30cf 0xffffffffffc3c30c

def z972 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffe0e3ffff3cf 0xbfffffe0e3ffff3c

def z973 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x61fc07f01fc0fc0a 0x661fc07f01fc0fc0

def z974 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x39f807c03fc0fc0b 0x239f807c03fc0fc0

def z975 : W := mkw 0xc1b407701540fc06 0x0c1b407701540fc0 0x39e407f03dc0fc0b 0x639e407f03dc0fc0

def z976 : W := mkw 0x00df900033000008 0x800df90003300000 0x7bfee0003fc00003 0x07bfee0003fc0000

def z977 : W := mkw 0xb29cf8d573d75d79 0xbb29cf8d573d75d7 0x421cf9f1c3c30c30 0x5421cf9f1c3c30c3

def z978 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x39fc07f03dc0f00b 0x239fc07f03dc0f00

def z979 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc3c00003 0xffaffffffc3c0000

def z980 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfffffffffc3cc3c4 0xffffffffffc3cc3c

def z981 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1fffffe23fffff 0xffe1fffffe23ffff

def z982 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfafffdfdc0000000 0x5fafffdfdc000000

def z983 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x79fc07f01fc03c0b 0x679fc07f01fc03c0

def z984 : W := mkw 0xa2d7d8c519ad4929 0x7a2d7d8c519ad492 0x25e51dcd1dcccf3a 0xe25e51dcd1dcccf3

def z985 : W := mkw 0x02dfb80abbbf0008 0xf02dfb80abbbf000 0xfbfff802ffff0007 0x1fbfff802ffff000

def z986 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x11f805c03fc0c003 0x011f805c03fc0c00

def z987 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfffff8003fff00f7 0x1fffff8003fff00f

def z988 : W := mkw 0x02d7980019ad0008 0x702d7980019ad000 0xa3e7f8001dcc0002 0x1a3e7f8001dcc000

def z989 : W := mkw 0x0243f88588bf0009 0x70243f88588bf000 0x8203f801c03f0004 0x18203f801c03f000

def z990 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x95e3040e3c3cf3cf 0x895e3040e3c3cf3c

def z991 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0x33fee0003df00002 0x033fee0003df0000

def z992 : W := mkw 0x10f79f3accedb6de 0x610f79f3accedb6d 0x21e51a32ddcc30c2 0x021e51a32ddcc30c

def z993 : W := mkw 0x2243f88f08bf03a9 0x72243f88f08bf03a 0x8603f80f003f03f4 0x98603f80f003f03f

def z994 : W := mkw 0xe1bc27703752fd26 0x8e1bc27703752fd2 0x79fc07f03ff0ff0b 0x679fc07f03ff0ff0

def z995 : W := mkw 0x0063960a8c28a28c 0x40063960a8c28a28 0xbde31e0efc3cf3cf 0xabde31e0efc3cf3c

def z996 : W := mkw 0x00f7d7af8828000f 0x400f7d7af8828000 0xfbffffffdc0c0002 0xffbffffffdc0c000

def z997 : W := mkw 0x02bcbe0a3797a28c 0xb02bcbe0a3797a28 0x461cfe0e03c3f3c8 0xb461cfe0e03c3f3c

def z998 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffffc0d3fffcf3f 0xffffffc0d3fffcf3

def z999 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffc0c3fffc307 0x1fbfffc0c3fffc30

def z1000 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xbafffffec0000000 0xabafffffec000000

def z1001 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfffffa03ffff30ff 0xbfffffa03ffff30f

def z1002 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde71e0e3c3cf3cf 0xbfde71e0e3c3cf3c

def z1003 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfe1ffa33c3cf3cff 0xffe1ffa33c3cf3cf

def z1004 : W := mkw 0x80bc076033004806 0x880bc07603300480 0x79fc07f03fc0cc0b 0x679fc07f03fc0cc0

def z1005 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x59f805c03fc0fc0b 0x659f805c03fc0fc0

def z1006 : W := mkw 0xb20828507bff5d70 0xfb20828507bff5d7 0x050000003fffffff 0x0050000003ffffff

def z1007 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x61fc01f01fc00c02 0x461fc01f01fc00c0

def z1008 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0x53fcf8003fc30000 0x153fcf8003fc3000

def z1009 : W := mkw 0x029cb00033120008 0x9029cb0003312000 0x7bfce0003fc00003 0x07bfce0003fc0000

def z1010 : W := mkw 0xc1b407701540fc06 0x0c1b407701540fc0 0x79fc07f01dc0fc0a 0x679fc07f01dc0fc0

def z1011 : W := mkw 0x00b4d7af8000000f 0x000b4d7af8000000 0x7afcffffc0000000 0xf7afcffffc000000

def z1012 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xce1cf9f1c2030c3d 0xfce1cf9f1c2030c3

def z1013 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1be5cd223fcf3f 0xffe1be5cd223fcf3

def z1014 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x79fc07c03fc0f00b 0x279fc07c03fc0f00

def z1015 : W := mkw 0x00bc07203700a006 0x800bc07203700a00 0x79fc07f03fc0f00b 0x679fc07f03fc0f00

def z1016 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xa5e3020e3c3cf3cf 0x8a5e3020e3c3cf3c

def z1017 : W := mkw 0x009c200033120000 0x8009c20003312000 0x7bfee0003ff00003 0x07bfee0003ff0000

def z1018 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0x63fcf8001fc30002 0x163fcf8001fc3000

def z1019 : W := mkw 0x02d7b80019bf0008 0x702d7b80019bf000 0xbbe7f8003dff0007 0x1bbe7f8003dff000

def z1020 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x35e3060e3c3cf3ca 0xa35e3060e3c3cf3c

def z1021 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x421cfdfdc0000000 0xf421cfdfdc000000

def z1022 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x42fcf9f1c0000000 0x542fcf9f1c000000

def z1023 : W := mkw 0xc1bc27703752fc06 0x8c1bc27703752fc0 0xfffee7f13ff3fc3f 0xffffee7f13ff3fc3

def z1024 : W := mkw 0x0000408500000001 0x0000040850000000 0xea1dfbf3c0000000 0xfea1dfbf3c000000

def z1025 : W := mkw 0x00f7d7af9100000f 0x000f7d7af9100000 0xfbffffffddc00002 0xffbffffffddc0000

def z1026 : W := mkw 0x82dfb8403bbf4808 0xf82dfb8403bbf480 0xfbfffdc03fffc007 0x1fbfffdc03fffc00

def z1027 : W := mkw 0x00b4d7a58000000f 0x000b4d7a58000000 0x62fcfbf1c0000000 0x562fcfbf1c000000

def z1028 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfc07f03fc0fc0f 0xefdfc07f03fc0fc0

def z1029 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffa003fff300f 0x3fbfffa003fff300

def z1030 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff831ffff0007 0x5fbfff831ffff000

def z1031 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x61fc03f03fc0fc0b 0x461fc03f03fc0fc0

def z1032 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0x79fc07f1ffc0fc3b 0x679fc07f1ffc0fc3

def z1033 : W := mkw 0x00b4d7a58000000f 0x000b4d7a58000000 0xfafdfff3c0000000 0xffafdfff3c000000

def z1034 : W := mkw 0x802806502640fc04 0x8802806502640fc0 0x79fc07f03fc0fc0b 0x679fc07f03fc0fc0

def z1035 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x7afdfff3c0000000 0x77afdfff3c000000

def z1036 : W := mkw 0xc1bc07703740fe86 0x8c1bc07703740fe8 0x7dfc07f03fc0ffcb 0x67dfc07f03fc0ffc

def z1037 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x11f805c03dc0f002 0x011f805c03dc0f00

def z1038 : W := mkw 0xe12047f50440fd27 0x0e12047f50440fd2 0x000007fc0000ff08 0x6000007fc0000ff0

def z1039 : W := mkw 0xc19c016033004802 0x8c19c01603300480 0x79fc01c03fc00003 0x079fc01c03fc0000

def z1040 : W := mkw 0x02f7d7af9928000f 0x502f7d7af9928000 0xfbffffffdc000000 0xffbffffffdc00000

def z1041 : W := mkw 0x00f7d7af8828028f 0x400f7d7af8828028 0xfeffffffe03cc3cd 0xffeffffffe03cc3c

def z1042 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x24051a33c3cf3cff 0xe24051a33c3cf3cf

def z1043 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde71e3ffe3fffff 0xffde71e3ffe3ffff

def z1044 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xea1df9f1c0000000 0x5ea1df9f1c000000

def z1045 : W := mkw 0x0243d88f88ad0009 0x70243d88f88ad000 0x8203f80fc00c0000 0x98203f80fc00c000

def z1046 : W := mkw 0xf108285077d7fd70 0xaf108285077d7fd7 0x050000003fffffff 0x0050000003ffffff

def z1047 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfffffffffc30c30d 0xffffffffffc30c30

def z1048 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x7dfc07f03ff0ff0f 0x67dfc07f03ff0ff0

def z1049 : W := mkw 0x3043688f48bf03f1 0x63043688f48bf03f 0x8603f80fc03f03f4 0x98603f80fc03f03f

def z1050 : W := mkw 0x12dfb80a7bbf02d8 0xf12dfb80a7bbf02d 0xfffff80fffff03f7 0x9fffff80fffff03f

def z1051 : W := mkw 0xc3dfb9603bbf480a 0xfc3dfb9603bbf480 0xfbfff9c03fff0007 0x1fbfff9c03fff000

def z1052 : W := mkw 0x2243f88508bf0129 0x72243f88508bf012 0x8203f80c003f0304 0x18203f80c003f030

def z1053 : W := mkw 0x00df980033850008 0xa00df98003385000 0xfbfff8003fcf0007 0x1fbfff8003fcf000

def z1054 : W := mkw 0x0043d08f80000009 0x00043d08f8000000 0xfa1fffffc0000000 0xffa1fffffc000000

def z1055 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x5a1cfdf1c0000000 0x75a1cfdf1c000000

def z1056 : W := mkw 0x02dfb80033970008 0xb02dfb8003397000 0xfbfff8003fc30003 0x1fbfff8003fc3000

def z1057 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fd07f03fccfc0f 0x6f9fd07f03fccfc0

def z1058 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfbfffffffc000003 0xffbfffffffc00000

def z1059 : W := mkw 0x41b407301540b406 0x041b407301540b40 0x21e407f01dc03002 0x621e407f01dc0300

def z1060 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x92fbffffc0000000 0xf92fbffffc000000

def z1061 : W := mkw 0x029cb8003bbf0008 0xf029cb8003bbf000 0x7bfcf8003fff0007 0x17bfcf8003fff000

def z1062 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xd3fff8003fff0004 0x1d3fff8003fff000

def z1063 : W := mkw 0x809c004033004800 0x8809c00403300480 0x79fc01c03fc00c03 0x479fc01c03fc00c0

def z1064 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0x13fae0003ff00003 0x013fae0003ff0000

def z1065 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0xfbffe0003ffc0007 0x0fbffe0003ffc000

def z1066 : W := mkw 0x00bc073033401406 0x800bc07303340140 0x79fc07f03fc03c0b 0x679fc07f03fc03c0

def z1067 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0x79fc07f2ffc0fccb 0x679fc07f2ffc0fcc

def z1068 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb9e3060e3c3cf3c7 0x0b9e3060e3c3cf3c

def z1069 : W := mkw 0x20f7d7af8000012f 0x020f7d7af8000012 0xfeffffffc0000330 0xffeffffffc000033

def z1070 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x71fc07f03fc0fc02 0x471fc07f03fc0fc0

def z1071 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xe3fff8001fff0006 0x1e3fff8001fff000

def z1072 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xe2fffbffc0000000 0xde2fffbffc000000

def z1073 : W := mkw 0x00b407300440b406 0x000b407300440b40 0x79fc07f03fc0fc0b 0x679fc07f03fc0fc0

def z1074 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde7060e3ffcf3cf 0xafde7060e3ffcf3c

def z1075 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xffffffffdc0c30cf 0xfffffffffdc0c30c

def z1076 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0x33fffffefc3cf3c2 0x033fffffefc3cf3c

def z1077 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xda1ae5cd2233cf30 0xfda1ae5cd2233cf3

def z1078 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x41fc01f01fc00c00 0x441fc01f01fc00c0

def z1079 : W := mkw 0x02dfb80a3bbf0288 0xf02dfb80a3bbf028 0xfffffc0e3fffc3cf 0xbfffffc0e3fffc3c

def z1080 : W := mkw 0x009c012033000002 0x8009c01203300000 0x79fc01f03fc00003 0x479fc01f03fc0000

def z1081 : W := mkw 0xc1bc077033405c06 0x8c1bc077033405c0 0x79fc07f03fc00c03 0x679fc07f03fc00c0

def z1082 : W := mkw 0xd30828507ffffc50 0xfd30828507ffffc5 0x050000003ffffcff 0x0050000003ffffcf

def z1083 : W := mkw 0x0063468f0c28a285 0x40063468f0c28a28 0xfffffffffc3cf3cf 0xffffffffffc3cf3c

def z1084 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x7afcf9f1c0000000 0x57afcf9f1c000000

def z1085 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc0030034 0xffeffffffc003003

def z1086 : W := mkw 0x009c280033970000 0xa009c28003397000 0xfbfff8003fff0007 0x1fbfff8003fff000

def z1087 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbfffffffc3c30c7 0xffbfffffffc3c30c

def z1088 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc03f03fc03c03 0x479fc03f03fc03c0

def z1089 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x22fdfbf2c0000000 0x022fdfbf2c000000

def z1090 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fc07f03fc3fc0f 0x7f9fc07f03fc3fc0

def z1091 : W := mkw 0x2243f88508bf0129 0x72243f88508bf012 0x8203f801003f0034 0x18203f801003f003

def z1092 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde3060f3c3cf3cf 0xffde3060f3c3cf3c

def z1093 : W := mkw 0x00d7d1af8000000b 0x000d7d1af8000000 0x421ef9fdc0000000 0x5421ef9fdc000000

def z1094 : W := mkw 0x00f7d7af8828028f 0x400f7d7af8828028 0xfaffffffc00c00c0 0xffaffffffc00c00c

def z1095 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x7bfef8003ff30003 0x17bfef8003ff3000

def z1096 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc2000c09 0xffaffffffc2000c0

def z1097 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xec051e3fc3cfffff 0xfec051e3fc3cffff

def z1098 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbffffffdc000000 0xffbffffffdc00000

def z1099 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffa303fff0007 0x7fbfffa303fff000

def z1100 : W := mkw 0x0243f88f88bf0289 0x70243f88f88bf028 0x8603f80fc03f03c4 0x98603f80fc03f03c

def z1101 : W := mkw 0xc12827702652fc06 0x8c12827702652fc0 0xda1ae7f02233fc0d 0x7da1ae7f02233fc0

def z1102 : W := mkw 0x004b28002abf0000 0xe004b28002abf000 0xfbfff8003fff0007 0x1fbfff8003fff000

def z1103 : W := mkw 0xc1bc077a3740fe86 0x8c1bc077a3740fe8 0xfdfe07fe3ff0ffcf 0xefdfe07fe3ff0ffc

def z1104 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc000000d 0xffeffffffc000000

def z1105 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8023fff00c7 0x9fffff8023fff00c

def z1106 : W := mkw 0x029cb80033970008 0xb029cb8003397000 0xfbfef8003ff30007 0x1fbfef8003ff3000

def z1107 : W := mkw 0x00b4d7af8000000f 0x000b4d7af8000000 0xea1dffffc0000000 0xfea1dffffc000000

def z1108 : W := mkw 0x009c200033120000 0x8009c20003312000 0x7bfce0003fc30003 0x17bfce0003fc3000

def z1109 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8003fff0c3f 0x1fffff8003fff0c3

def z1110 : W := mkw 0x00d7d1a58000000b 0x000d7d1a58000000 0xc21ff9f1c0000000 0x5c21ff9f1c000000

def z1111 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xde1ae5cd223fffff 0xfde1ae5cd223ffff

def z1112 : W := mkw 0x002047af80000007 0x0002047af8000000 0xfa1fffffc0000000 0xffa1fffffc000000

def z1113 : W := mkw 0x00df90003b280008 0xc00df90003b28000 0xfbfff8003ffc0007 0x1fbfff8003ffc000

def z1114 : W := mkw 0xc12007700440fc06 0x0c12007700440fc0 0x79e407f03fc0fc0b 0x679e407f03fc0fc0

def z1115 : W := mkw 0xb02046df4440fff5 0x0b02046df4440fff 0x040007ffc000fff8 0xe040007ffc000fff

def z1116 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde31e0ffc3cf3cf 0xbbde31e0ffc3cf3c

def z1117 : W := mkw 0x0243f88f88bf0009 0x70243f88f88bf000 0x8203f80c003f0004 0x18203f80c003f000

def z1118 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfd07f33fcffcff 0xffdfd07f33fcffcf

def z1119 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0xfdfd1ff3ffc0fcfb 0xffdfd1ff3ffc0fcf

def z1120 : W := mkw 0xe1bc27703752fd26 0x8e1bc27703752fd2 0xfdfe07fc3ff3ff3f 0xefdfe07fc3ff3ff3

def z1121 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfaffffffc00c0007 0xffaffffffc00c000

def z1122 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xc61ae5cd0233cf3c 0xfc61ae5cd0233cf3

def z1123 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0x161ae5cd2233cf3d 0xe161ae5cd2233cf3

def z1124 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfffae5cd3e33cf3f 0xffffae5cd3e33cf3

def z1125 : W := mkw 0xa2dfb8403bbf4928 0xfa2dfb8403bbf492 0xfffffdc03fffcf3f 0x7fffffdc03fffcf3

def z1126 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xfbfffffffc0cf0cb 0xffbfffffffc0cf0c

def z1127 : W := mkw 0x02dfb80a3bbf0008 0xf02dfb80a3bbf000 0xfbfff80e3fff0007 0x9fbfff80e3fff000

def z1128 : W := mkw 0x00b4d7a58000000f 0x000b4d7a58000000 0x421cfff1c0000000 0x7421cfff1c000000

def z1129 : W := mkw 0x00d7d1af8000000b 0x000d7d1af8000000 0xfafff9ffc0000000 0xdfafff9ffc000000

def z1130 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfc051e33e3cffcff 0xffc051e33e3cffcf

def z1131 : W := mkw 0xc19c017033405c02 0x8c19c017033405c0 0x79fc03f03fc03c0b 0x679fc03f03fc03c0

def z1132 : W := mkw 0x00f7d7af8400a00f 0x000f7d7af8400a00 0xfaffffffc000f008 0xffaffffffc000f00

def z1133 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde3040c3c3cf3cf 0x0bde3040c3c3cf3c

def z1134 : W := mkw 0x809c004033004800 0x8809c00403300480 0x79fc05c03fc0c003 0x079fc05c03fc0c00

def z1135 : W := mkw 0x009c000033000000 0x8009c00003300000 0x79fc05c03fc00003 0x679fc05c03fc0000

def z1136 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe8051a33c3cf3cf2 0xfe8051a33c3cf3cf

def z1137 : W := mkw 0x00f7d7af8828000f 0x400f7d7af8828000 0xfbfffffffc300000 0xffbfffffffc30000

def z1138 : W := mkw 0xb008285062d75d70 0xab008285062d75d7 0x0400000023f3cf3d 0x00400000023f3cf3

def z1139 : W := mkw 0xa00860c533124921 0x8a00860c53312492 0xdf1ae5cd3ff3cf3f 0xfdf1ae5cd3ff3cf3

def z1140 : W := mkw 0x12dfb8007bbf0058 0xf12dfb8007bbf005 0xfffff803ffff0cff 0xffffff803ffff0cf

def z1141 : W := mkw 0x0000408500000001 0x0000040850000000 0xde1ae5cd2233cf3d 0xfde1ae5cd2233cf3

def z1142 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfff803ffff0007 0x9fbfff803ffff000

def z1143 : W := mkw 0x00d7d1a58000000b 0x000d7d1a58000000 0x52fef9f1c0000000 0x552fef9f1c000000

def z1144 : W := mkw 0x00b447a500000007 0x000b447a50000000 0xfaffffffc0000000 0xffaffffffc000000

def z1145 : W := mkw 0xc1bc077a3740fe86 0x8c1bc077a3740fe8 0x79fc07f23fc0fccb 0x679fc07f23fc0fcc

def z1146 : W := mkw 0xc1bc27703752fc06 0x8c1bc27703752fc0 0x7bfee7f03ff0fc0b 0x67bfee7f03ff0fc0

def z1147 : W := mkw 0xd1bc07707740fc56 0x8d1bc07707740fc5 0x7dfc07f03fc0fcfb 0x67dfc07f03fc0fcf

def z1148 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x7afffffec0000000 0x67afffffec000000

def z1149 : W := mkw 0xc12047f50440fc07 0x0c12047f50440fc0 0x000007fd0000fc08 0xe000007fd0000fc0

def z1150 : W := mkw 0x02d7b80019bf0008 0x702d7b80019bf000 0xfbfff8001dff0006 0x1fbfff8001dff000

def z1151 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xffffffffdc3c33c6 0xfffffffffdc3c33c

def z1152 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x9de2040c3c3cf3cf 0xa9de2040c3c3cf3c

def z1153 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x59fc05f03fc0cc09 0x659fc05f03fc0cc0

def z1154 : W := mkw 0xc1b407701540fc06 0x0c1b407701540fc0 0x69e407f01fc0fc0b 0x669e407f01fc0fc0

def z1155 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfc071e3fc3cf3cff 0xffc071e3fc3cf3cf

def z1156 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xda1ae5cd2233cf35 0x5da1ae5cd2233cf3

def z1157 : W := mkw 0x00bc072033000006 0x800bc07203300000 0x79fc05c03fc00003 0x079fc05c03fc0000

def z1158 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0x421cf9f1c2030c30 0x5421cf9f1c2030c3

def z1159 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdfd1ff3ffc3fc3f 0xffdfd1ff3ffc3fc3

def z1160 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x63fdf8003fff0007 0x163fdf8003fff000

def z1161 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xc21fffffc0000000 0xfc21fffffc000000

def z1162 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xe4051a33c3cf3cf6 0xde4051a33c3cf3cf

def z1163 : W := mkw 0xa008204022124920 0x8a00820402212492 0xec051a33e233cf3d 0xfec051a33e233cf3

def z1164 : W := mkw 0x002006000c28a284 0x4002006000c28a28 0xbde2060c3c3cf3cf 0xabde2060c3c3cf3c

def z1165 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0x63fdfbf3dc0c30c2 0x563fdfbf3dc0c30c

def z1166 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x7dfc07fc3fc0ff0b 0xe7dfc07fc3fc0ff0

def z1167 : W := mkw 0x1243f88fc8bf0059 0x71243f88fc8bf005 0x8603f80fc03f00f4 0x98603f80fc03f00f

def z1168 : W := mkw 0x0063072a8c28a286 0x40063072a8c28a28 0xbde3063efc3cf3cf 0xabde3063efc3cf3c

def z1169 : W := mkw 0x004300000c28a280 0x4004300000c28a28 0xbde3040c3c3cf3cf 0xabde3040c3c3cf3c

def z1170 : W := mkw 0x41bc07303740b406 0x841bc07303740b40 0x79fc07f03fc03003 0x679fc07f03fc0300

def z1171 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x95e3060e3c3cf3cc 0xa95e3060e3c3cf3c

def z1172 : W := mkw 0x0043000a0c28a280 0x40043000a0c28a28 0xbde3000e3c3cf3cf 0x8bde3000e3c3cf3c

def z1173 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc00c00c4 0xffeffffffc00c00c

def z1174 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x12fefdfcc0000000 0x012fefdfcc000000

def z1175 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xfde51a33ffcf3cff 0xffde51a33ffcf3cf

def z1176 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xc4051a33c3cf3cfc 0xfc4051a33c3cf3cf

def z1177 : W := mkw 0x02dfb0003b3a0008 0xd02dfb0003b3a000 0x53fee0003ff00000 0x053fee0003ff0000

def z1178 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde3060f3c3ff3ff 0xbbde3060f3c3ff3f

def z1179 : W := mkw 0xa00860c522124921 0x8a00860c52212492 0xfe1be7cf2233cf3d 0xffe1be7cf2233cf3

def z1180 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x11fc05f03dc0c000 0x011fc05f03dc0c00

def z1181 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x79fc07f03fc0c003 0x679fc07f03fc0c00

def z1182 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xbde71e3efc3cf3cf 0xabde71e3efc3cf3c

def z1183 : W := mkw 0xc1b407701540fc06 0x0c1b407701540fc0 0x21e407f01dc0f002 0x021e407f01dc0f00

def z1184 : W := mkw 0x00f7d7af8c28a28f 0x400f7d7af8c28a28 0xffffffffdc0cf3ca 0xfffffffffdc0cf3c

def z1185 : W := mkw 0xb06b2e5a6efffff4 0xeb06b2e5a6efffff 0xbde3060e3fffffff 0xabde3060e3ffffff

def z1186 : W := mkw 0x0020060a0c28a284 0x40020060a0c28a28 0x3de0060e3c3cf3cf 0xa3de0060e3c3cf3c

def z1187 : W := mkw 0x00d7d08500000009 0x000d7d0850000000 0xfaffffffc0000000 0xffaffffffc000000

def z1188 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x79fc05c03fc0cc0b 0x679fc05c03fc0cc0

def z1189 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xfdff07fe3ffcffcf 0xefdff07fe3ffcffc

def z1190 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xec051a33e3ffffff 0xfec051a33e3fffff

def z1191 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x35e3060e3c3cf3cf 0x035e3060e3c3cf3c

def z1192 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0xf9fc07f13fc0fc0b 0xff9fc07f13fc0fc0

def z1193 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x7dfc07f03fc3fc3f 0x67dfc07f03fc3fc3

def z1194 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfde3060e3e3cffcf 0xefde3060e3e3cffc

def z1195 : W := mkw 0x1000081040c51450 0x21000081040c5145 0xa4051a33c3cf3cff 0x9a4051a33c3cf3cf

def z1196 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x7bfff8003ffc0003 0x07bfff8003ffc000

def z1197 : W := mkw 0xf19c69f573d75d73 0xaf19c69f573d75d7 0x421cf9f1c3c30c30 0x5421cf9f1c3c30c3

def z1198 : W := mkw 0x00f7d7af8828028f 0x400f7d7af8828028 0xfeffffffc03c33cf 0xffeffffffc03c33c

def z1199 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x64051a33c3cf3cfa 0xf64051a33c3cf3cf

def z1200 : W := mkw 0x00f7d7af8828000f 0x400f7d7af8828000 0xfaffffffc03c0004 0xffaffffffc03c000

def z1201 : W := mkw 0x00f797200000000e 0x000f797200000000 0xfafffff3c0000000 0xffafffff3c000000

def z1202 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfeffffffc0000c38 0xffeffffffc0000c3

def z1203 : W := mkw 0x00b4d7a58000000f 0x000b4d7a58000000 0x52fcfdf1c0000000 0x552fcfdf1c000000

def z1204 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0x52feffffc0000000 0xf52feffffc000000

def z1205 : W := mkw 0x00f7d7af8000028f 0x000f7d7af8000028 0xfeffffffc00003c0 0xffeffffffc00003c

def z1206 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xfffbe60e3c3cf3cf 0xbfffbe60e3c3cf3c

def z1207 : W := mkw 0xc1bc077ab740fc06 0x8c1bc077ab740fc0 0x79fc07f2ffc0fc0b 0x679fc07f2ffc0fc0

def z1208 : W := mkw 0x02d7b80019bf0008 0x702d7b80019bf000 0xebe7f8001fff0007 0x1ebe7f8001fff000

def z1209 : W := mkw 0x00f7d7af8400a00f 0x000f7d7af8400a00 0xfffffffffc0cf0cf 0xffffffffffc0cf0c

def z1210 : W := mkw 0x0000408500000001 0x0000040850000000 0xfe1fffffe03cf3cf 0xffe1fffffe03cf3c

def z1211 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x51fc05c03fc0c000 0x051fc05c03fc0c00

def z1212 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x11e2040c3c3cf3c2 0x011e2040c3c3cf3c

def z1213 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfbfffa023fff0007 0xbfbfffa023fff000

def z1214 : W := mkw 0x02dfb80a3bbf0288 0xf02dfb80a3bbf028 0xfffffa0e3fff33cf 0xbfffffa0e3fff33c

def z1215 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xebfdf8001fcf0007 0x1ebfdf8001fcf000

def z1216 : W := mkw 0xc1bc077a3740fe86 0x8c1bc077a3740fe8 0xfdfd07fe3fccffcf 0xefdfd07fe3fccffc

def z1217 : W := mkw 0x41f7d7af9500a00f 0x041f7d7af9500a00 0xfbffffffdc000000 0xffbffffffdc00000

def z1218 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xc21ef9fdc0000000 0xdc21ef9fdc000000

def z1219 : W := mkw 0x1000081040c51450 0x21000081040c5145 0x64051a33c3cf3cff 0x564051a33c3cf3cf

def z1220 : W := mkw 0x02dfb8003bbf0288 0xf02dfb8003bbf028 0xfffff8003fff03c7 0x1fffff8003fff03c

def z1221 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0x73fff8003fff0002 0x173fff8003fff000

def z1222 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0x15e2060e3c3cf3cf 0xa15e2060e3c3cf3c

def z1223 : W := mkw 0xc1bc07603700e806 0x8c1bc07603700e80 0x31fc05c03dc0c002 0x031fc05c03dc0c00

def z1224 : W := mkw 0x0063d7af8000000f 0x00063d7af8000000 0xda1bffffc0000000 0xfda1bffffc000000

def z1225 : W := mkw 0xb008285062d75d70 0xab008285062d75d7 0x0400000003cf3cff 0x00400000003cf3cf

def z1226 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fc07f3ffc0fc0b 0xe79fc07f3ffc0fc0

def z1227 : W := mkw 0x02dfb8003bbf0008 0xf02dfb8003bbf000 0xfffff8003fff000f 0xbfffff8003fff000

def z1228 : W := mkw 0x00d7d1af8000000b 0x000d7d1af8000000 0xda1ffdffc0000000 0xfda1ffdffc000000

def z1229 : W := mkw 0x00b4d7af8400a28f 0x000b4d7af8400a28 0x461cffffc000f3c8 0xf461cffffc000f3c

def z1230 : W := mkw 0x00f7d7af8828028f 0x400f7d7af8828028 0xfaffffffc0300300 0xffaffffffc030030

def z1231 : W := mkw 0x00f7d7af8000000f 0x000f7d7af8000000 0xfafffbf3c0000000 0x5fafffbf3c000000

def z1232 : W := mkw 0x0094d1a58000000b 0x00094d1a58000000 0xfa1fffffc0000000 0xffa1fffffc000000

def z1233 : W := mkw 0x00f7d7af8c28a00f 0x400f7d7af8c28a00 0xfbfffffffc3cf00f 0xffbfffffffc3cf00

def z1234 : W := mkw 0x0063060a0c28a284 0x40063060a0c28a28 0xb5e3060e3c3cf3c6 0x8b5e3060e3c3cf3c

def z1235 : W := mkw 0x00f7d7af8400a28f 0x000f7d7af8400a28 0xfffffffffc00f3cb 0xffffffffffc00f3c

def z1236 : W := mkw 0x00f7d7af8400a00f 0x000f7d7af8400a00 0xfbfffffffc00c000 0xffbfffffffc00c00

def z1237 : W := mkw 0x02dfb80a3bbf0288 0xf02dfb80a3bbf028 0xfbfff80c3fff0307 0x1fbfff80c3fff030

def z1238 : W := mkw 0x82dfb8403bbf4808 0xf82dfb8403bbf480 0xfffffdcc3fffcf0f 0xffffffdcc3fffcf0

def z1239 : W := mkw 0xc1bc07703740fc06 0x8c1bc07703740fc0 0x79fd07f23fccfccb 0x679fd07f23fccfcc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z5,z6])],[(0,[z9,z0,z1,z2,z4,z5,z6]),(0,[z0,z10,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z12,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z5,z14]),(0,[z15,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z16]),(0,[z0,z1,z2,z17,z4,z5,z6]),(0,[z0,z1,z18,z17,z4,z5,z6]),(0,[z0,z1,z2,z19,z4,z5,z6])],[(0,[z20,z0,z1,z2,z4,z5,z21]),(0,[z0,z1,z22,z2,z4,z5,z6]),(0,[z23,z0,z1,z24,z4,z5,z6])],[(0,[z0,z1,z25,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z4,z5,z6])],[(0,[z27,z0,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z29,z4,z5,z6]),(0,[z0,z1,z2,z30,z4,z5,z6]),(0,[z0,z1,z31,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z6])],[(0,[z33,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z34,z5,z6]),(0,[z0,z35,z1,z2,z4,z36,z6]),(0,[z0,z1,z2,z4,z37,z6,z38])],[(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z40,z6]),(0,[z0,z11,z2,z4,z5,z41,z6]),(0,[z0,z1,z2,z4,z5,z42,z6]),(0,[z0,z43,z1,z18,z4,z5,z6]),(0,[z0,z1,z2,z44,z4,z5,z6])],[(0,[z0,z43,z28,z2,z4,z5,z6]),(1,[z0,z45,z2,z4,z5,z6]),(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z47,z6]),(0,[z0,z1,z2,z48,z4,z5,z6]),(0,[z0,z1,z2,z49,z4,z5,z6])]],
   [[(0,[z0,z1,z50,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z51,z52])],[(0,[z0,z28,z2,z4,z53,z5,z6]),(0,[z0,z1,z2,z54,z4,z5,z6]),(0,[z0,z1,z4,z55,z5,z56,z6]),(0,[z0,z1,z2,z4,z57,z5,z6]),(0,[z58,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z59,z4,z5,z6])],[(0,[z60,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z61,z5,z62,z6]),(0,[z0,z1,z2,z4,z5,z6,z63]),(0,[z64,z0,z26,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z65,z5])],[(0,[z66,z0,z1,z2,z4,z5,z6]),(1,[z0,z22,z2,z4,z5,z6]),(0,[z13,z1,z2,z4,z5,z62,z6]),(0,[z0,z1,z67,z2,z4,z5,z6]),(0,[z0,z1,z68,z2,z4,z5,z6]),(0,[z23,z0,z69,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z36,z6]),(0,[z70,z0,z1,z2,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z6]),(0,[z0,z72,z1,z2,z4,z5,z6]),(1,[z73,z1,z2,z4,z61,z6]),(0,[z0,z1,z2,z4,z5,z74,z38]),(0,[z75,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z76]),(1,[z77,z0,z1,z55,z5,z6]),(0,[z0,z1,z2,z4,z78,z5,z6]),(0,[z79,z0,z1,z2,z4,z5,z52]),(0,[z80,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z81,z5,z6])],[(0,[z0,z1,z2,z82,z4,z5,z6]),(0,[z0,z1,z2,z4,z37,z5,z6])],[(0,[z0,z28,z83,z2,z4,z5,z6]),(0,[z0,z1,z84,z2,z4,z5,z6]),(1,[z0,z1,z85,z4,z5,z6]),(0,[z0,z86,z2,z4,z5,z6,z87]),(0,[z0,z1,z2,z49,z4,z41,z6])]],
   [[(0,[z0,z1,z88,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z41,z6]),(0,[z73,z0,z1,z2,z4,z61,z6])],[(0,[z0,z1,z2,z4,z5,z89,z6]),(0,[z0,z90,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z91]),(0,[z20,z0,z1,z2,z4,z92,z6]),(1,[z0,z1,z2,z4,z5,z14]),(0,[z0,z26,z1,z2,z93,z5,z6]),(0,[z0,z94,z1,z2,z4,z5,z6]),(0,[z95,z0,z1,z2,z4,z5,z6]),(0,[z96,z0,z1,z2,z4,z8,z5])],[(0,[z0,z97,z11,z2,z4,z5,z6]),(0,[z98,z0,z1,z2,z4,z5,z6]),(0,[z27,z0,z99,z2,z4,z5,z6]),(1,[z27,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z100,z6]),(0,[z0,z1,z2,z4,z5,z101,z6]),(0,[z0,z1,z2,z102,z4,z5,z6]),(0,[z103,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z104]),(0,[z0,z1,z2,z4,z105,z5,z6])],[(0,[z0,z1,z2,z4,z106,z5,z6]),(0,[z77,z0,z1,z4,z55,z5,z6]),(0,[z0,z1,z2,z4,z107,z5,z6]),(0,[z0,z1,z2,z4,z108,z5,z6])],[(0,[z0,z1,z109,z2,z4,z5,z6]),(0,[z0,z110,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z111,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z6]),(0,[z0,z1,z2,z4,z113,z5,z6]),(0,[z114,z0,z1,z2,z4,z5,z74]),(0,[z115,z0,z1,z116,z4,z5,z6]),(0,[z0,z1,z2,z4,z117,z5,z118])],[(0,[z0,z1,z119,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z87,z52]),(0,[z0,z1,z2,z120,z4,z5,z6]),(0,[z0,z121,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z122,z6]),(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z0,z124,z2,z116,z4,z5,z6]),(0,[z0,z1,z83,z18,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z125]),(0,[z64,z126,z0,z2,z4,z5,z6]),(0,[z127,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z128,z2,z4,z5,z129])],[(0,[z0,z86,z28,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z5,z130]),(1,[z0,z1,z131,z2,z4,z5]),(0,[z132,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z133,z5,z6]),(0,[z0,z134,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z29,z4,z135,z5,z6]),(0,[z0,z1,z2,z4,z5,z136,z6]),(1,[z0,z1,z2,z4,z137,z6])],[(0,[z0,z11,z2,z116,z4,z5,z6]),(1,[z0,z1,z2,z4,z138,z6]),(0,[z64,z0,z1,z2,z4,z139,z6]),(0,[z140,z0,z1,z2,z4,z5,z6]),(0,[z0,z35,z2,z4,z117,z5,z6]),(1,[z0,z86,z2,z4,z5,z87])],[(0,[z0,z1,z2,z4,z141,z5,z6]),(1,[z0,z1,z142,z4,z5,z6]),(0,[z0,z124,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z143]),(0,[z0,z1,z2,z4,z5,z144,z6]),(0,[z0,z145,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z146,z5,z6]),(0,[z0,z1,z2,z147,z4,z5,z6]),(0,[z0,z1,z18,z147,z4,z5,z6]),(0,[z0,z43,z1,z2,z4,z5,z148]),(0,[z149,z0,z1,z2,z4,z5,z6])],[(0,[z0,z11,z2,z4,z5,z130,z6]),(0,[z64,z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z151,z6]),(0,[z0,z1,z2,z4,z152,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z153,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z49,z53,z6])],[(1,[z28,z2,z4,z135,z5,z6]),(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z23,z156,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z157,z6]),(0,[z158,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z159,z6]),(0,[z0,z1,z160,z2,z4,z5,z6])]],
   [[(0,[z64,z0,z1,z102,z4,z5,z6])],[(0,[z0,z28,z2,z4,z161,z5,z6]),(1,[z162,z0,z1,z4,z56,z6])],[(0,[z0,z163,z1,z2,z4,z5,z6]),(0,[z0,z1,z164,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z165]),(0,[z0,z1,z2,z4,z5,z6,z166])],[(0,[z167,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z168,z6]),(0,[z0,z1,z2,z4,z169,z5,z6])],[(1,[z0,z1,z119,z4,z5,z6]),(0,[z0,z1,z2,z4,z170,z5,z6]),(0,[z0,z171,z1,z2,z4,z5,z6])],[(0,[z11,z1,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z172,z5,z6]),(0,[z0,z11,z2,z4,z5,z6,z52]),(0,[z64,z0,z11,z2,z4,z5,z6]),(0,[z173,z0,z1,z2,z4,z5,z6]),(0,[z174,z0,z1,z2,z4,z5,z6]),(0,[z175,z0,z1,z2,z4,z5,z6]),(0,[z115,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z176,z5,z6]),(0,[z0,z177,z1,z2,z4,z5,z6])],[(0,[z178,z0,z1,z2,z4,z5,z6]),(0,[z179,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z180,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z181,z2,z4,z5,z6]),(0,[z0,z1,z182,z2,z4,z5,z6]),(0,[z162,z0,z1,z2,z4,z56,z6]),(0,[z0,z1,z69,z2,z4,z5,z6]),(1,[z0,z1,z24,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z183,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z184])],[(0,[z0,z11,z2,z4,z5,z62,z6]),(0,[z0,z11,z2,z4,z5,z185,z6]),(0,[z0,z1,z2,z4,z5,z185,z6]),(0,[z186,z0,z1,z2,z4,z5,z6]),(0,[z187,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z188,z6]),(0,[z0,z1,z2,z4,z189,z5,z6]),(0,[z190,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z52,z38])],[(0,[z0,z11,z18,z2,z4,z5,z6]),(0,[z0,z1,z2,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z117,z53,z6])],[(0,[z0,z28,z2,z4,z135,z5,z6]),(0,[z0,z11,z86,z2,z4,z5,z6]),(0,[z0,z1,z192,z2,z4,z5,z6]),(0,[z0,z1,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z4,z193,z5,z6]),(0,[z0,z1,z2,z4,z105,z8,z6])],[(0,[z0,z1,z2,z194,z4,z5,z6]),(0,[z0,z1,z2,z195,z4,z5,z6]),(0,[z0,z1,z2,z196,z4,z5,z6]),(0,[z0,z1,z2,z4,z197,z5,z6]),(0,[z0,z1,z198,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z6,z87]),(0,[z0,z11,z2,z4,z55,z5,z6]),(0,[z0,z199,z1,z2,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z5,z130]),(0,[z200,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z128,z2,z4,z105,z5])],[(0,[z0,z1,z2,z4,z8,z5,z74]),(0,[z0,z1,z2,z4,z5,z201,z6]),(0,[z202,z0,z1,z2,z4,z5,z6]),(0,[z0,z203,z1,z2,z4,z5,z6])],[(0,[z0,z11,z2,z4,z5,z6,z204]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z27,z73,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z205,z5,z6]),(1,[z0,z1,z4,z5,z206,z6]),(0,[z0,z1,z207,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z208,z5,z6]),(0,[z0,z1,z2,z209,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z210]),(0,[z0,z1,z2,z4,z105,z37,z6])]],
   [[(0,[z27,z1,z28,z2,z4,z5,z6]),(0,[z211,z0,z1,z2,z4,z5,z6]),(1,[z0,z199,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z213]),(0,[z0,z1,z2,z4,z5,z6,z214]),(1,[z0,z1,z128,z4,z5,z129]),(0,[z0,z1,z2,z4,z5,z215,z6])],[(0,[z216,z0,z1,z2,z4,z5,z6]),(0,[z20,z27,z1,z2,z4,z5,z6]),(0,[z217,z0,z1,z2,z4,z5,z6]),(0,[z73,z0,z199,z2,z4,z5,z6]),(0,[z0,z218,z1,z2,z116,z4,z5]),(0,[z219,z0,z1,z2,z4,z5,z6]),(1,[z0,z69,z2,z4,z5,z6]),(0,[z220,z0,z2,z4,z5,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z221]),(0,[z222,z0,z1,z2,z4,z5,z6])],[(0,[z23,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z223]),(0,[z224,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z225,z5,z6]),(0,[z0,z1,z226,z2,z4,z5,z6]),(0,[z227,z0,z1,z2,z4,z5,z6])],[(0,[z228,z0,z1,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z6,z74]),(0,[z229,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z230,z6]),(0,[z0,z1,z131,z2,z116,z4,z5]),(0,[z0,z1,z2,z4,z5,z231,z6]),(0,[z0,z43,z1,z2,z4,z5,z6])],[(0,[z0,z11,z232,z2,z4,z5,z6]),(1,[z0,z192,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z233,z5]),(0,[z0,z1,z234,z2,z4,z5,z6]),(1,[z0,z43,z1,z4,z5,z204]),(1,[z0,z1,z2,z4,z5,z215]),(0,[z0,z1,z2,z4,z5,z6,z235]),(0,[z0,z1,z2,z4,z5,z236,z6])],[(0,[z39,z0,z11,z2,z4,z5,z6]),(1,[z114,z1,z2,z4,z5,z130]),(0,[z0,z1,z237,z2,z4,z5,z6]),(0,[z0,z43,z1,z2,z4,z5,z129]),(0,[z0,z1,z2,z44,z5,z148,z6]),(0,[z0,z1,z238,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z5,z6])],[(0,[z0,z1,z240,z2,z4,z5,z6]),(0,[z211,z0,z1,z25,z4,z5,z6]),(0,[z241,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z242,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z243]),(0,[z0,z1,z2,z4,z244,z5,z6]),(0,[z0,z1,z232,z4,z55,z5,z6])],[(0,[z0,z245,z28,z2,z4,z5,z6]),(0,[z79,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z4,z5,z6]),(0,[z0,z1,z2,z4,z246,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z247]),(0,[z0,z1,z2,z4,z248,z5,z6]),(0,[z0,z43,z1,z4,z5,z6,z204]),(0,[z0,z1,z2,z4,z249,z5,z6])],[(0,[z0,z11,z2,z4,z250,z5,z6]),(0,[z0,z1,z2,z4,z5,z251,z6]),(0,[z20,z1,z2,z4,z135,z5,z6]),(0,[z252,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z253,z2,z4,z5,z6])],[(0,[z254,z0,z1,z2,z4,z5,z6]),(0,[z0,z43,z1,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z139,z5,z6]),(0,[z0,z255,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z256,z5,z6]),(0,[z0,z257,z1,z2,z4,z5,z6])],[(0,[z0,z1,z147,z4,z5,z56,z6]),(0,[z0,z1,z2,z258,z4,z5,z6]),(0,[z0,z124,z1,z232,z4,z5,z6]),(0,[z0,z35,z1,z2,z4,z117,z6]),(0,[z259,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z135,z5,z41,z6]),(0,[z0,z260,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z130,z52]),(0,[z0,z1,z2,z261,z4,z5,z6]),(0,[z0,z1,z2,z262,z4,z5,z6])],[(0,[z13,z0,z72,z2,z4,z5,z6]),(0,[z0,z1,z2,z263,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z264,z6]),(0,[z162,z0,z1,z4,z5,z56,z6]),(0,[z0,z1,z2,z4,z5,z6,z265])],[(0,[z266,z0,z1,z2,z4,z5,z6]),(0,[z267,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z268]),(0,[z0,z1,z2,z4,z269,z5,z6]),(0,[z0,z1,z2,z4,z270,z5,z6]),(0,[z0,z1,z2,z4,z271,z5,z6])]],
   [[(0,[z0,z28,z2,z4,z117,z5,z6]),(0,[z77,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z272,z5,z6]),(0,[z0,z1,z2,z4,z273,z5,z6]),(0,[z0,z1,z2,z4,z274,z5,z6])],[(0,[z0,z1,z2,z4,z275,z5,z6]),(0,[z0,z1,z2,z4,z5,z276,z6]),(1,[z0,z1,z232,z4,z172,z6])],[(0,[z0,z1,z2,z4,z277,z5,z6]),(0,[z13,z0,z1,z2,z4,z61,z6]),(0,[z13,z0,z1,z2,z4,z62,z6])],[(0,[z278,z0,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z8,z5,z6]),(0,[z267,z0,z1,z147,z4,z5,z6]),(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z280,z5,z6]),(0,[z281,z0,z1,z2,z4,z5,z6]),(0,[z96,z0,z2,z4,z5,z51,z6]),(1,[z156,z1,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z49,z5,z6]),(0,[z0,z1,z2,z4,z282,z5,z6])],[(0,[z0,z11,z2,z17,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z123,z0,z1,z2,z4,z5,z74]),(0,[z0,z1,z83,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z283,z5,z6]),(1,[z0,z1,z284,z4,z5,z6])],[(0,[z0,z1,z2,z4,z285,z5,z6]),(0,[z0,z286,z1,z2,z4,z5,z6])],[(0,[z0,z11,z25,z2,z4,z5,z6]),(0,[z0,z1,z2,z287,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z288,z6])],[(0,[z115,z0,z1,z232,z4,z5,z6]),(0,[z0,z1,z83,z4,z55,z5,z6]),(0,[z0,z1,z2,z289,z4,z5,z6]),(0,[z0,z1,z2,z4,z290,z5,z6]),(0,[z0,z1,z2,z4,z291,z5,z6]),(0,[z0,z1,z44,z4,z292,z5,z6])]],
   [[(0,[z0,z28,z2,z4,z5,z56,z6]),(1,[z0,z1,z2,z4,z5,z293]),(0,[z162,z0,z43,z1,z4,z5,z6]),(0,[z220,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z37,z294,z5,z6])],[(0,[z0,z11,z2,z44,z4,z5,z6]),(0,[z0,z1,z25,z4,z55,z5,z6]),(0,[z0,z295,z1,z2,z4,z5,z6]),(0,[z0,z86,z1,z128,z2,z4,z5]),(0,[z0,z1,z18,z4,z5,z129,z6]),(0,[z0,z1,z2,z4,z5,z129,z6]),(0,[z0,z1,z2,z4,z296,z5,z6]),(0,[z0,z257,z1,z4,z5,z6,z38])],[(0,[z0,z11,z2,z49,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z297,z6]),(0,[z162,z0,z1,z2,z4,z5,z298]),(0,[z299,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z53,z5,z41,z6])],[(0,[z96,z0,z28,z2,z4,z5,z6]),(0,[z300,z0,z1,z2,z4,z5,z6]),(0,[z0,z43,z1,z2,z4,z5,z130]),(1,[z0,z1,z2,z4,z139,z6]),(1,[z0,z26,z2,z93,z5,z6]),(1,[z0,z1,z301,z4,z5,z6]),(0,[z0,z1,z2,z4,z302,z5,z6])],[(0,[z0,z124,z1,z116,z4,z5,z6]),(0,[z115,z0,z83,z2,z4,z5,z6]),(1,[z64,z0,z2,z303,z5,z6]),(0,[z0,z1,z2,z4,z294,z5,z6])],[(1,[z0,z1,z2,z4,z5,z304]),(0,[z0,z43,z1,z2,z4,z105,z5]),(0,[z79,z0,z1,z2,z4,z5,z148])],[(0,[z267,z211,z1,z2,z4,z5,z6]),(0,[z305,z0,z1,z2,z4,z5,z6]),(1,[z0,z72,z2,z4,z5,z6]),(1,[z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z4,z5,z206,z6,z87])],[(0,[z306,z0,z1,z2,z4,z5,z6]),(0,[z307,z0,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z308,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z130,z38])],[(0,[z0,z35,z28,z2,z4,z5,z6]),(0,[z0,z309,z1,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z37,z5,z6]),(0,[z0,z1,z310,z2,z4,z5,z6]),(0,[z123,z114,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z5,z6])],[(0,[z311,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z102,z4,z5,z6])],[(0,[z0,z1,z2,z312,z4,z5,z6]),(0,[z0,z1,z2,z4,z313,z5,z6]),(0,[z0,z1,z2,z308,z4,z5,z6]),(0,[z0,z1,z2,z4,z314,z5,z6])],[(0,[z73,z1,z2,z4,z135,z5,z6]),(0,[z0,z26,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z315,z6]),(0,[z0,z1,z2,z4,z316,z5,z6])],[(0,[z0,z11,z2,z4,z105,z5,z6]),(0,[z115,z0,z11,z2,z4,z5,z6]),(0,[z317,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z318,z2,z4,z5,z6]),(0,[z0,z1,z319,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z320,z5,z6])],[(0,[z0,z1,z2,z321,z4,z5,z6]),(0,[z0,z1,z2,z4,z322,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z323]),(0,[z0,z324,z1,z2,z4,z5,z6]),(0,[z325,z0,z1,z2,z4,z5,z6])],[(1,[z0,z11,z2,z4,z5,z6]),(0,[z0,z11,z128,z2,z4,z5,z6]),(0,[z326,z0,z1,z2,z4,z5,z6]),(0,[z327,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z128,z2,z4,z5,z6])]],
   [[(0,[z73,z0,z11,z2,z4,z5,z6]),(0,[z328,z0,z1,z2,z4,z5,z6]),(1,[z220,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z329,z5,z6])],[(0,[z114,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z330]),(0,[z0,z218,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z331,z6]),(0,[z0,z332,z1,z2,z4,z5,z6]),(0,[z333,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z334,z5,z6]),(1,[z0,z1,z2,z44,z5,z148])],[(0,[z0,z1,z2,z4,z5,z335,z6]),(0,[z336,z0,z1,z2,z4,z5,z6]),(0,[z211,z1,z2,z147,z4,z5,z6]),(0,[z337,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z338,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z339]),(0,[z0,z1,z2,z4,z233,z5,z56]),(0,[z0,z1,z2,z49,z53,z5,z6]),(0,[z0,z1,z2,z4,z8,z37,z5])],[(0,[z20,z0,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z6,z340]),(1,[z0,z310,z2,z4,z5,z6]),(0,[z0,z341,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z342,z5,z6]),(0,[z0,z1,z2,z4,z343,z5,z6])],[(0,[z344,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z131,z2,z4,z5,z6]),(0,[z0,z35,z2,z4,z303,z5,z6]),(0,[z0,z1,z2,z345,z4,z5,z6]),(0,[z79,z0,z1,z2,z5,z6,z52])],[(0,[z77,z0,z28,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z130,z6,z74]),(0,[z346,z0,z1,z2,z4,z5,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z162,z0,z1,z2,z4,z172,z6])],[(0,[z0,z11,z2,z147,z4,z5,z6]),(0,[z348,z0,z1,z2,z4,z5,z6]),(0,[z0,z349,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z350,z6])],[(0,[z126,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z351,z6]),(0,[z0,z1,z2,z4,z5,z148,z6])]],
   [[(0,[z0,z11,z1,z2,z4,z5,z6]),(1,[z27,z28,z2,z4,z5,z6]),(0,[z211,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z135,z5,z6]),(0,[z0,z1,z2,z4,z5,z352,z6])],[(0,[z0,z28,z2,z4,z5,z130,z6]),(0,[z216,z0,z11,z2,z4,z5,z6])],[(0,[z267,z0,z1,z2,z4,z5,z353]),(0,[z0,z43,z1,z2,z4,z5,z74]),(0,[z0,z1,z2,z4,z354,z5,z6]),(0,[z0,z355,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z356,z6])],[(0,[z357,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z358,z4,z5,z6]),(0,[z0,z0,z11,z2,z4,z5,z6]),(0,[z211,z0,z310,z2,z4,z5,z6]),(0,[z211,z0,z1,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z359,z6]),(0,[z0,z1,z2,z4,z8,z5,z52]),(0,[z0,z1,z2,z4,z360,z5,z6])],[(0,[z361,z11,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z362,z6]),(0,[z0,z1,z25,z4,z5,z129,z6]),(0,[z0,z1,z2,z4,z5,z363,z6]),(0,[z162,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z364,z6]),(0,[z0,z1,z2,z4,z5,z365,z6]),(0,[z0,z366,z1,z2,z4,z5,z6]),(0,[z0,z367,z1,z2,z4,z5,z6])],[(0,[z0,z1,z147,z4,z55,z5,z6]),(0,[z0,z1,z2,z4,z5,z368,z6]),(0,[z79,z0,z1,z2,z4,z5,z6])],[(0,[z123,z0,z192,z2,z4,z5,z6]),(0,[z369,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z25,z232,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z370]),(0,[z0,z1,z371,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z14]),(0,[z114,z0,z372,z2,z4,z5,z6]),(0,[z373,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z374,z4,z5,z6])],[(0,[z0,z28,z2,z375,z4,z5,z6]),(0,[z361,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z232,z147,z4,z5,z6]),(0,[z27,z1,z2,z4,z5,z62,z6]),(1,[z115,z0,z83,z4,z5,z6])],[(0,[z0,z1,z2,z376,z4,z5,z6]),(1,[z20,z1,z2,z135,z5,z6]),(0,[z0,z1,z2,z4,z377,z5,z6]),(0,[z0,z1,z2,z4,z53,z62,z6]),(0,[z0,z378,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z44,z4,z5,z52])],[(0,[z0,z1,z2,z4,z379,z5,z6]),(0,[z267,z0,z380,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z5,z36,z6]),(0,[z126,z0,z35,z2,z4,z5,z6]),(0,[z381,z0,z1,z2,z4,z5,z6])],[(0,[z0,z11,z35,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z382]),(0,[z383,z0,z1,z2,z4,z5,z6]),(0,[z384,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z92,z6]),(0,[z0,z1,z2,z4,z5,z6,z125]),(0,[z126,z0,z2,z93,z4,z5,z6])],[(0,[z361,z39,z1,z2,z4,z5,z6]),(0,[z0,z11,z2,z93,z4,z5,z6]),(0,[z0,z1,z128,z2,z4,z5,z130]),(0,[z0,z1,z2,z4,z385,z5,z6]),(0,[z0,z386,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z5,z204])],[(0,[z0,z28,z18,z2,z4,z5,z6]),(0,[z0,z387,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z28,z2,z4,z5,z51,z6]),(0,[z278,z0,z1,z2,z4,z5,z6]),(0,[z388,z0,z1,z2,z4,z5,z6]),(0,[z389,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z390,z2,z4,z5,z6]),(0,[z0,z391,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z392,z4,z5,z6])],[(0,[z0,z1,z393,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z394,z5,z6])],[(0,[z115,z0,z124,z2,z4,z5,z6]),(0,[z0,z43,z1,z4,z172,z5,z6])],[(0,[z0,z395,z1,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z6,z204]),(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z396,z5,z6]),(0,[z64,z391,z1,z2,z4,z5,z6]),(0,[z0,z1,z397,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z4,z53,z6])],[(0,[z73,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z398]),(0,[z0,z1,z2,z399,z4,z5,z6]),(0,[z0,z1,z2,z4,z400,z5,z6]),(0,[z0,z1,z2,z401,z4,z5,z6])],[(0,[z114,z0,z28,z2,z4,z5,z6]),(0,[z0,z11,z26,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z402,z5,z6]),(0,[z23,z367,z1,z2,z4,z5,z6]),(0,[z0,z403,z1,z2,z4,z5,z6])],[(1,[z0,z404,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z405,z5,z6]),(0,[z0,z1,z2,z4,z406,z5,z6]),(0,[z0,z1,z4,z117,z5,z351,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z407,z6]),(0,[z0,z28,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z408,z5,z6]),(0,[z96,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z37,z38])],[(0,[z0,z1,z380,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z409,z6]),(0,[z0,z1,z2,z4,z410,z5,z6]),(0,[z0,z1,z2,z411,z4,z5,z6]),(0,[z0,z1,z128,z232,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z353]),(0,[z20,z0,z84,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z412,z6]),(0,[z0,z43,z1,z4,z55,z5,z6])],[(0,[z0,z1,z2,z49,z135,z5,z6]),(0,[z0,z1,z2,z4,z413,z5,z6]),(0,[z414,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z415,z4,z5,z6])],[(0,[z416,z0,z1,z2,z4,z5,z6]),(0,[z417,z0,z1,z2,z4,z5,z6]),(0,[z0,z11,z2,z29,z4,z5,z6]),(0,[z0,z124,z1,z4,z5,z129,z6]),(0,[z23,z0,z324,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z6,z38]),(0,[z0,z1,z2,z4,z5,z418,z6]),(0,[z0,z1,z2,z419,z4,z5,z6]),(0,[z0,z1,z2,z4,z117,z41,z6]),(1,[z96,z0,z2,z4,z5,z51]),(0,[z96,z0,z1,z128,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z6,z420]),(0,[z60,z0,z11,z2,z4,z5,z6]),(0,[z421,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z422,z1,z2,z4,z5,z6]),(0,[z0,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z36,z41,z6]),(0,[z0,z43,z1,z128,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z423,z6]),(1,[z0,z424,z2,z4,z5,z6]),(0,[z425,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z426]),(0,[z0,z427,z1,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z4,z5,z265]),(0,[z0,z1,z2,z4,z5,z6,z428])]],
   [[(0,[z211,z0,z404,z2,z4,z5,z6]),(0,[z0,z429,z1,z2,z4,z5,z6]),(0,[z430,z0,z1,z2,z4,z5,z6])],[(0,[z431,z0,z1,z2,z4,z5,z6]),(0,[z0,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z432,z5,z6]),(0,[z0,z1,z2,z433,z4,z5,z6]),(0,[z0,z434,z1,z2,z4,z5,z6])],[(0,[z0,z11,z2,z4,z53,z5,z6]),(0,[z0,z1,z2,z4,z435,z5,z6]),(0,[z0,z1,z436,z2,z4,z5,z6]),(0,[z437,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z5,z6]),(1,[z0,z257,z1,z4,z5,z6])],[(0,[z0,z28,z2,z4,z303,z5,z6]),(1,[z0,z380,z2,z4,z5,z6]),(0,[z13,z0,z1,z308,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z118]),(0,[z0,z1,z2,z4,z438,z117,z5]),(0,[z0,z1,z2,z4,z5,z6,z439]),(0,[z0,z1,z4,z172,z5,z129,z6])],[(0,[z0,z28,z2,z4,z61,z5,z6]),(0,[z440,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z441,z5,z6])],[(0,[z64,z0,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z36,z6]),(0,[z0,z1,z128,z2,z4,z5,z74]),(0,[z0,z1,z85,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z442]),(0,[z0,z1,z2,z4,z5,z36,z6]),(0,[z0,z1,z2,z4,z37,z5,z38])],[(1,[z0,z1,z287,z4,z5,z6]),(0,[z443,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z444,z5,z6]),(0,[z96,z0,z86,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z445,z6]),(0,[z0,z1,z2,z4,z5,z148,z87]),(0,[z0,z1,z2,z4,z292,z5,z6])],[(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z11,z83,z2,z4,z5,z6]),(0,[z0,z447,z1,z2,z4,z5,z6]),(0,[z115,z0,z1,z4,z5,z129,z6]),(0,[z0,z86,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z448,z6]),(0,[z0,z1,z2,z5,z148,z6,z52])]],
   [[(0,[z0,z28,z2,z3,z4,z5,z6]),(0,[z0,z28,z2,z4,z8,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z114,z0,z1,z287,z4,z5,z6]),(0,[z0,z1,z2,z4,z438,z5,z6])],[(0,[z0,z28,z2,z17,z4,z5,z6]),(0,[z123,z0,z11,z2,z4,z5,z6]),(0,[z449,z0,z1,z2,z4,z5,z6]),(0,[z0,z450,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z105,z5,z38])],[(0,[z0,z1,z2,z4,z5,z451,z6]),(0,[z13,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z452,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z453]),(0,[z0,z454,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z204,z38]),(0,[z455,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z456]),(1,[z0,z1,z4,z5,z6,z457])],[(0,[z0,z11,z2,z4,z5,z129,z6]),(0,[z0,z458,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z49,z29,z5,z6]),(0,[z114,z0,z341,z2,z4,z5,z6]),(1,[z126,z0,z2,z4,z36,z6]),(0,[z0,z1,z2,z4,z5,z51,z148]),(0,[z77,z0,z1,z2,z17,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z459]),(1,[z0,z1,z4,z294,z5,z6])],[(0,[z0,z1,z460,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z148,z74]),(0,[z461,z0,z1,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z41,z6]),(0,[z0,z28,z2,z44,z4,z5,z6]),(0,[z0,z462,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z457])],[(0,[z126,z0,z11,z2,z4,z5,z6]),(0,[z27,z0,z463,z2,z4,z5,z6]),(0,[z0,z464,z1,z2,z4,z5,z6])]],
   [[(0,[z465,z0,z1,z2,z4,z5,z6]),(0,[z0,z11,z11,z2,z4,z5,z6]),(0,[z73,z0,z466,z2,z4,z5,z6]),(0,[z64,z0,z2,z4,z117,z5,z6]),(0,[z0,z1,z2,z4,z5,z467,z6])],[(0,[z0,z1,z2,z4,z5,z468,z6]),(0,[z0,z1,z2,z4,z469,z5,z6]),(0,[z0,z1,z470,z2,z4,z5,z6])],[(0,[z23,z0,z28,z2,z4,z5,z6]),(1,[z123,z1,z2,z4,z5,z74]),(0,[z0,z2,z4,z303,z5,z36,z6])],[(0,[z167,z0,z1,z2,z4,z5,z6]),(0,[z0,z471,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z472,z4,z5,z6])],[(0,[z0,z1,z2,z4,z473,z5,z6]),(0,[z474,z0,z1,z2,z4,z5,z6]),(0,[z475,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z476,z6]),(0,[z0,z1,z2,z4,z477,z5,z6])],[(0,[z478,z0,z1,z2,z4,z5,z6]),(0,[z479,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z480])],[(0,[z39,z0,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z37,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z481]),(0,[z0,z1,z482,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z442]),(0,[z0,z1,z2,z483,z4,z5,z6]),(0,[z0,z1,z17,z4,z55,z5,z6]),(0,[z0,z484,z1,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z5,z41,z6])],[(0,[z0,z1,z2,z485,z4,z5,z6]),(0,[z0,z486,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z28,z88,z2,z4,z5,z6]),(0,[z0,z45,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z487,z6])],[(0,[z0,z28,z2,z4,z5,z89,z6]),(0,[z0,z1,z2,z4,z161,z5,z6]),(0,[z488,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z489]),(0,[z0,z1,z2,z4,z5,z6,z490])],[(1,[z361,z11,z2,z4,z5,z6]),(0,[z0,z11,z43,z2,z4,z5,z6]),(1,[z211,z1,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z491,z5,z6]),(0,[z0,z1,z2,z4,z492,z5,z6]),(1,[z0,z2,z4,z5,z467,z6])],[(0,[z60,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6]),(0,[z0,z83,z2,z116,z4,z5,z6]),(0,[z0,z1,z2,z494,z4,z5,z6]),(1,[z367,z1,z2,z4,z5,z6]),(0,[z495,z0,z1,z2,z4,z5,z6])],[(0,[z66,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z496,z5,z6]),(0,[z0,z1,z497,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z498,z5,z6]),(0,[z0,z1,z2,z4,z5,z499,z6]),(0,[z0,z1,z116,z4,z55,z5,z6]),(0,[z64,z500,z1,z2,z4,z5,z6])],[(0,[z1,z28,z2,z4,z135,z5,z6]),(0,[z0,z90,z1,z2,z4,z5,z6]),(0,[z0,z501,z1,z2,z4,z5,z6]),(0,[z502,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z503,z6]),(0,[z0,z1,z2,z4,z5,z504,z6]),(0,[z0,z1,z2,z4,z5,z6,z505])],[(0,[z267,z0,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z506,z5,z6]),(0,[z0,z507,z1,z2,z4,z5,z6]),(0,[z0,z1,z372,z2,z4,z5,z6]),(0,[z115,z0,z1,z83,z4,z5,z6]),(1,[z0,z1,z4,z5,z351,z6]),(0,[z96,z0,z1,z2,z4,z5,z87]),(0,[z77,z0,z1,z18,z4,z5,z6])]],
   [[(0,[z0,z1,z508,z2,z4,z5,z6]),(0,[z0,z1,z2,z509,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z510,z6]),(0,[z123,z0,z163,z2,z4,z5,z6]),(0,[z511,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z512,z5,z6])],[(0,[z0,z28,z2,z116,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z21]),(0,[z513,z0,z1,z2,z4,z5,z6]),(1,[z0,z324,z2,z4,z5,z6]),(1,[z23,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z514,z4,z5,z6])],[(0,[z0,z109,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z148,z6]),(0,[z0,z1,z18,z2,z55,z5,z6]),(0,[z0,z43,z1,z2,z4,z5,z204])],[(0,[z0,z11,z2,z4,z135,z5,z6]),(0,[z0,z1,z2,z4,z515,z5,z6])],[(0,[z0,z110,z28,z2,z4,z5,z6]),(0,[z0,z516,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z304])],[(0,[z517,z0,z1,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z6,z518]),(0,[z0,z1,z2,z4,z5,z6,z518]),(0,[z0,z11,z2,z4,z5,z6,z87]),(0,[z0,z1,z2,z4,z5,z519,z6]),(0,[z0,z1,z2,z4,z5,z51,z6]),(0,[z0,z1,z2,z4,z5,z6,z87]),(0,[z520,z0,z1,z2,z4,z5,z6])],[(1,[z0,z124,z116,z4,z5,z6]),(0,[z0,z1,z2,z4,z521,z5,z6]),(1,[z391,z1,z2,z4,z5,z6]),(0,[z0,z1,z301,z4,z117,z5,z6]),(0,[z0,z1,z18,z2,z17,z5,z6])],[(0,[z0,z1,z2,z4,z138,z5,z6])]],
   [[(0,[z361,z1,z2,z4,z135,z5,z6]),(0,[z522,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z523,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z524,z6]),(0,[z0,z1,z2,z4,z5,z525,z6])],[(0,[z0,z245,z1,z2,z4,z5,z6]),(0,[z526,z0,z1,z2,z4,z5,z6]),(1,[z0,z372,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z527,z6])],[(0,[z0,z124,z28,z2,z4,z5,z6]),(0,[z0,z528,z1,z4,z5,z6,z87]),(0,[z529,z0,z1,z2,z4,z5,z6])],[(0,[z530,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z531,z6]),(0,[z0,z43,z1,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z532,z5,z6]),(0,[z0,z1,z2,z533,z4,z5,z6]),(0,[z0,z1,z2,z4,z105,z8,z5])],[(0,[z0,z1,z2,z4,z5,z6,z534]),(0,[z0,z1,z2,z4,z5,z6,z74]),(0,[z0,z1,z2,z4,z535,z5,z6])],[(0,[z0,z28,z2,z4,z172,z5,z6]),(0,[z0,z28,z2,z4,z5,z6,z52]),(0,[z0,z1,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z376,z4,z5,z6]),(0,[z0,z11,z124,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z61,z6]),(0,[z0,z2,z93,z4,z117,z5,z6]),(0,[z0,z536,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z538,z6]),(0,[z0,z539,z1,z2,z4,z5,z6]),(0,[z0,z1,z284,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z105,z8])],[(0,[z0,z1,z2,z4,z5,z6,z540]),(0,[z541,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z542,z2,z4,z5,z6]),(0,[z0,z86,z1,z2,z4,z5,z87]),(0,[z543,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z544,z4,z5,z6]),(0,[z545,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z546,z6]),(0,[z0,z1,z547,z2,z4,z5,z6]),(0,[z548,z0,z1,z2,z4,z5,z6])]],
   [[],[(0,[z0,z28,z2,z4,z5,z62,z6]),(1,[z0,z163,z2,z4,z5,z6]),(0,[z549,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z128,z2,z4,z37,z5])],[(0,[z1,z2,z4,z135,z5,z62,z6]),(0,[z0,z1,z2,z4,z550,z5,z6]),(0,[z0,z1,z2,z4,z5,z551,z6])],[(0,[z0,z28,z2,z93,z4,z5,z6]),(0,[z0,z1,z552,z2,z4,z5,z6]),(0,[z0,z1,z2,z553,z4,z5,z6]),(0,[z0,z1,z2,z17,z4,z5,z214])],[(0,[z0,z1,z232,z2,z4,z56,z6])],[(0,[z0,z28,z2,z4,z55,z5,z6]),(0,[z115,z0,z28,z2,z4,z5,z6]),(0,[z554,z0,z1,z2,z4,z5,z6]),(0,[z555,z0,z1,z2,z4,z5,z6]),(0,[z0,z556,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z557,z5,z6]),(0,[z0,z1,z2,z4,z558,z5,z6])],[(0,[z0,z1,z2,z4,z559,z5,z6]),(0,[z27,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z560,z6]),(0,[z0,z1,z2,z4,z5,z6,z561]),(0,[z96,z0,z1,z2,z4,z5,z51])],[(1,[z0,z28,z2,z4,z5,z6]),(0,[z446,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z562,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z563,z5,z6]),(0,[z0,z463,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z117,z5,z6]),(1,[z0,z1,z18,z17,z5,z6])],[(0,[z0,z1,z564,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z565,z5,z6]),(0,[z566,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z567,z5,z6]),(0,[z0,z1,z128,z4,z5,z129,z6])],[(0,[z0,z1,z2,z4,z5,z568,z6]),(1,[z79,z0,z1,z2,z5,z52])],[(0,[z0,z1,z99,z2,z4,z5,z6]),(0,[z115,z0,z1,z4,z5,z56,z6]),(0,[z0,z1,z2,z4,z569,z5,z6]),(0,[z0,z1,z128,z2,z4,z5,z52])],[(0,[z0,z458,z11,z2,z4,z5,z6]),(0,[z27,z1,z2,z29,z4,z5,z6]),(0,[z0,z1,z2,z570,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z571]),(0,[z0,z1,z2,z49,z4,z53,z6])],[(0,[z0,z28,z232,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z138,z6]),(0,[z0,z1,z2,z572,z4,z5,z6]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z574])],[(0,[z20,z0,z1,z142,z4,z5,z6]),(0,[z575,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z576,z5,z6])],[(0,[z0,z1,z2,z4,z8,z5,z129]),(0,[z23,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z211,z0,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z56,z6]),(0,[z577,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z195,z5,z6]),(0,[z0,z1,z2,z4,z5,z130,z148]),(0,[z64,z0,z1,z2,z93,z5,z6]),(0,[z0,z1,z18,z4,z5,z56,z6]),(0,[z0,z1,z2,z4,z5,z56,z6]),(0,[z0,z1,z2,z578,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z129,z38])],[(0,[z0,z1,z2,z579,z4,z5,z6]),(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z41,z6]),(0,[z0,z1,z2,z581,z4,z5,z6]),(0,[z64,z0,z1,z2,z303,z5,z6]),(0,[z582,z0,z1,z2,z4,z5,z6])],[(0,[z39,z1,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z583]),(0,[z584,z0,z1,z2,z4,z5,z6])],[(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z585,z6]),(0,[z0,z1,z2,z4,z586,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z6])],[(0,[z0,z1,z2,z4,z587,z5,z6]),(0,[z0,z1,z2,z588,z4,z5,z6]),(0,[z0,z1,z232,z18,z4,z5,z6])],[(0,[z0,z1,z147,z4,z5,z129,z6]),(0,[z0,z424,z1,z2,z4,z5,z6]),(1,[z0,z99,z2,z4,z5,z6]),(0,[z115,z0,z43,z1,z4,z5,z6]),(0,[z0,z589,z1,z2,z4,z5,z6]),(0,[z0,z86,z1,z2,z4,z5,z51]),(0,[z0,z590,z1,z2,z4,z5,z6]),(0,[z0,z1,z128,z2,z4,z5,z204])],[(0,[z0,z1,z2,z4,z53,z36,z6]),(1,[z0,z1,z4,z292,z5,z6]),(0,[z0,z1,z374,z2,z4,z5,z6]),(0,[z0,z1,z2,z591,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z592,z6]),(0,[z126,z0,z2,z4,z5,z36,z6]),(0,[z162,z0,z1,z4,z5,z129,z6]),(0,[z23,z0,z1,z2,z4,z41,z6])]],
   [[(0,[z20,z0,z1,z119,z4,z5,z6]),(0,[z0,z1,z466,z2,z4,z5,z6]),(0,[z593,z0,z1,z2,z4,z5,z6])],[(0,[z361,z0,z28,z2,z4,z5,z6]),(0,[z594,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z298]),(0,[z0,z1,z2,z4,z5,z595,z6])],[(0,[z20,z0,z1,z2,z29,z5,z6]),(0,[z0,z596,z1,z2,z4,z5,z6]),(0,[z0,z1,z597,z2,z4,z5,z6]),(0,[z162,z0,z1,z232,z4,z5,z6]),(0,[z0,z1,z4,z5,z129,z6,z204]),(0,[z0,z598,z1,z2,z4,z5,z6]),(0,[z0,z599,z1,z2,z4,z5,z6])],[(0,[z600,z0,z1,z2,z4,z5,z6]),(0,[z601,z0,z1,z2,z4,z5,z6]),(0,[z77,z0,z1,z2,z55,z5,z6]),(0,[z602,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z603,z5,z6]),(0,[z604,z0,z1,z2,z4,z5,z6])],[(0,[z267,z0,z1,z2,z4,z5,z6]),(0,[z0,z605,z1,z2,z4,z5,z6]),(1,[z13,z1,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z606,z5,z6])],[(0,[z73,z0,z1,z2,z4,z62,z6]),(1,[z0,z341,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z607,z5,z6]),(0,[z77,z0,z1,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z4,z5,z215])],[(0,[z0,z28,z25,z2,z4,z5,z6]),(0,[z114,z0,z1,z85,z4,z5,z6]),(0,[z114,z1,z2,z4,z5,z130,z6]),(0,[z0,z1,z2,z4,z5,z608,z6]),(0,[z162,z0,z1,z2,z4,z5,z304]),(0,[z0,z1,z2,z4,z5,z6,z609])],[(1,[z500,z1,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z303,z5,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z611,z6])]],
   [[(1,[z0,z1,z2,z195,z5,z6]),(0,[z0,z2,z4,z117,z5,z36,z6])],[(0,[z0,z28,z2,z4,z5,z40,z6]),(0,[z0,z28,z2,z4,z5,z129,z6]),(0,[z0,z10,z1,z2,z4,z5,z6]),(0,[z0,z1,z612,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z353]),(0,[z123,z1,z2,z4,z5,z6,z74]),(0,[z0,z613,z1,z2,z4,z5,z6]),(0,[z0,z43,z1,z2,z4,z37,z5])],[(0,[z0,z28,z2,z49,z4,z5,z6]),(0,[z13,z73,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z34,z5,z6]),(1,[z0,z466,z2,z4,z5,z6]),(0,[z614,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z615,z6]),(0,[z0,z1,z2,z17,z4,z5,z231])],[(0,[z0,z1,z2,z4,z5,z6,z340]),(0,[z267,z0,z1,z25,z4,z5,z6]),(0,[z616,z0,z1,z2,z4,z5,z6]),(0,[z64,z0,z2,z4,z303,z5,z6]),(0,[z96,z0,z43,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z617,z6])],[(0,[z9,z0,z28,z2,z4,z5,z6]),(0,[z0,z618,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z619,z6]),(0,[z0,z1,z284,z4,z37,z5,z6])],[(0,[z0,z1,z620,z2,z4,z5,z6]),(0,[z0,z1,z25,z18,z4,z5,z6]),(0,[z0,z1,z621,z2,z4,z5,z6]),(0,[z0,z1,z301,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z622,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z623])],[(0,[z0,z26,z28,z2,z4,z5,z6]),(1,[z0,z84,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z624]),(0,[z0,z1,z2,z116,z4,z5,z6]),(0,[z0,z1,z18,z116,z4,z5,z6]),(0,[z625,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z55,z5,z129,z6]),(0,[z626,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z148,z38]),(0,[z627,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z628,z5,z6]),(0,[z0,z124,z1,z83,z4,z5,z6]),(0,[z0,z35,z26,z2,z4,z5,z6]),(0,[z629,z0,z1,z2,z4,z5,z6]),(0,[z630,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z162,z0,z11,z2,z4,z5,z6]),(0,[z267,z0,z1,z2,z4,z5,z631]),(0,[z0,z1,z2,z632,z4,z5,z6])],[(0,[z79,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z633,z5,z6]),(0,[z0,z1,z2,z4,z5,z130,z6]),(0,[z0,z1,z634,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z635]),(0,[z0,z1,z2,z4,z636,z5,z6]),(1,[z0,z1,z2,z4,z5,z214]),(0,[z0,z1,z2,z4,z5,z6,z637])],[(0,[z0,z1,z2,z4,z5,z631,z6]),(0,[z0,z1,z2,z142,z4,z5,z6]),(0,[z0,z1,z2,z4,z34,z5,z6]),(0,[z126,z0,z1,z2,z4,z117,z6]),(0,[z0,z1,z2,z4,z5,z6,z118]),(0,[z23,z0,z1,z638,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z639,z6]),(0,[z0,z43,z1,z2,z4,z5,z52])],[(0,[z0,z1,z25,z4,z5,z56,z6]),(0,[z0,z1,z2,z4,z640,z5,z6]),(0,[z0,z1,z2,z4,z5,z641,z6])],[(0,[z0,z28,z2,z4,z105,z5,z6]),(0,[z0,z1,z2,z4,z5,z642,z6]),(0,[z0,z43,z86,z1,z2,z4,z5]),(0,[z0,z86,z1,z2,z4,z8,z5]),(0,[z0,z1,z638,z2,z4,z5,z6])],[(0,[z0,z11,z2,z4,z493,z5,z6]),(0,[z267,z1,z25,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z643,z6]),(0,[z0,z1,z2,z4,z5,z6,z644]),(0,[z0,z1,z2,z4,z5,z645,z6])],[(0,[z0,z28,z128,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z646,z5,z6]),(0,[z0,z1,z2,z4,z5,z647,z6]),(0,[z545,z0,z11,z2,z4,z5,z6]),(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z649,z5,z6]),(0,[z0,z1,z4,z5,z6,z457,z38])]],
   [[(0,[z20,z0,z424,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z650,z5,z6])],[(0,[z0,z309,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z375,z4,z5,z6]),(0,[z0,z1,z2,z4,z651,z5,z6]),(0,[z0,z1,z2,z652,z4,z5,z6])],[(0,[z361,z27,z1,z2,z4,z5,z6]),(0,[z0,z97,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z172,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z52])],[(1,[z11,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z653]),(0,[z0,z1,z2,z4,z5,z654,z6])],[(0,[z64,z0,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z655,z5,z6]),(0,[z0,z1,z4,z5,z56,z6,z204])],[(0,[z0,z404,z1,z2,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z442,z6]),(0,[z656,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z657,z4,z5,z6]),(0,[z0,z1,z374,z44,z4,z5,z6])],[(0,[z0,z28,z2,z147,z4,z5,z6]),(0,[z658,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z62,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z659,z5,z6]),(0,[z64,z0,z1,z2,z4,z137,z6]),(0,[z126,z0,z1,z2,z4,z36,z6]),(0,[z0,z1,z2,z660,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z148,z6]),(0,[z27,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z43,z124,z1,z4,z5,z6]),(0,[z661,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z18,z2,z4,z5,z6]),(0,[z662,z0,z1,z2,z4,z5,z6]),(0,[z663,z0,z1,z2,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z24,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z265]),(0,[z0,z2,z4,z5,z467,z41,z6]),(0,[z0,z1,z2,z4,z8,z5,z148])]],
   [[(0,[z0,z11,z2,z4,z5,z51,z6]),(0,[z664,z0,z1,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z135,z5,z6])],[(0,[z123,z0,z28,z2,z4,z5,z6])],[(0,[z13,z0,z28,z2,z4,z5,z6]),(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z371,z4,z5,z6]),(0,[z0,z1,z2,z4,z666,z5,z6]),(0,[z0,z1,z2,z4,z5,z667,z6]),(0,[z0,z1,z2,z4,z55,z5,z6]),(0,[z0,z1,z2,z4,z668,z5,z6]),(0,[z0,z1,z232,z2,z4,z172,z6]),(0,[z669,z0,z1,z2,z4,z5,z6])],[(0,[z670,z0,z1,z2,z4,z5,z6]),(0,[z96,z0,z11,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z5,z409]),(0,[z671,z0,z1,z2,z4,z5,z6]),(0,[z0,z672,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z673])],[(1,[z39,z28,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z293]),(0,[z0,z528,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z204])],[(1,[z0,z218,z1,z2,z4,z5]),(0,[z0,z1,z128,z4,z5,z56,z6]),(0,[z0,z1,z232,z4,z172,z5,z6]),(0,[z0,z1,z2,z44,z4,z5,z148])],[(0,[z0,z11,z2,z4,z5,z531,z6])],[(0,[z126,z0,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z6,z74]),(0,[z267,z0,z45,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z137,z6]),(0,[z0,z1,z2,z4,z5,z206,z6]),(0,[z96,z0,z1,z2,z4,z5,z38]),(0,[z0,z1,z2,z4,z5,z6,z674])]],
   [[(0,[z0,z1,z2,z4,z675,z5,z6]),(0,[z0,z11,z28,z2,z4,z5,z6]),(0,[z676,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z631]),(0,[z73,z1,z2,z4,z61,z5,z6]),(0,[z0,z2,z93,z4,z303,z5,z6]),(0,[z0,z1,z2,z677,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z678,z2,z4,z5,z6])],[(0,[z0,z1,z2,z679,z4,z5,z6]),(0,[z0,z2,z4,z5,z51,z6,z87]),(0,[z0,z1,z232,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z233,z5,z6])],[(0,[z0,z28,z2,z4,z379,z5,z6]),(0,[z0,z1,z2,z4,z62,z41,z6]),(0,[z0,z1,z2,z4,z680,z5,z6]),(0,[z0,z124,z1,z4,z5,z56,z6]),(0,[z0,z681,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z682])],[(0,[z0,z11,z683,z2,z4,z5,z6]),(0,[z0,z1,z683,z2,z4,z5,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z438,z5]),(0,[z79,z0,z1,z2,z44,z5,z6])],[(0,[z162,z0,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z6,z38]),(0,[z685,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z686,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z38])],[(0,[z361,z0,z1,z2,z4,z5,z6]),(0,[z0,z11,z2,z553,z4,z5,z6])],[(0,[z440,z0,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z250,z5,z6]),(0,[z0,z1,z2,z687,z4,z5,z6]),(1,[z0,z528,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z688]),(0,[z0,z1,z232,z4,z5,z6,z204]),(0,[z0,z1,z2,z4,z689,z5,z6]),(0,[z0,z1,z2,z4,z8,z6,z38])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z21]),(0,[z0,z1,z2,z4,z5,z6,z690]),(0,[z0,z1,z2,z4,z5,z691,z6]),(1,[z0,z1,z2,z4,z5,z231])],[(0,[z0,z1,z2,z692,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z693,z6])],[(0,[z1,z25,z2,z147,z4,z5,z6]),(0,[z0,z1,z2,z694,z4,z5,z6]),(1,[z0,z1,z371,z4,z5,z6]),(0,[z0,z1,z2,z4,z695,z5,z6]),(0,[z0,z1,z2,z4,z5,z74,z52]),(0,[z0,z1,z4,z172,z5,z56,z6]),(0,[z0,z1,z2,z4,z5,z6,z696]),(0,[z0,z1,z2,z4,z5,z6,z697])],[(0,[z20,z0,z11,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z303,z5,z6]),(0,[z0,z11,z2,z4,z117,z5,z6]),(1,[z0,z1,z2,z4,z5,z409]),(0,[z0,z1,z2,z4,z303,z5,z6]),(0,[z0,z1,z128,z2,z4,z5,z148])],[(0,[z0,z11,z2,z4,z61,z5,z6]),(0,[z0,z1,z2,z4,z5,z293,z6]),(0,[z20,z0,z1,z2,z135,z5,z6]),(0,[z13,z0,z22,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z5,z6]),(0,[z698,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z699,z6]),(0,[z0,z1,z700,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z5,z56]),(0,[z0,z701,z1,z2,z4,z5,z6]),(0,[z0,z1,z702,z2,z4,z5,z6])],[(0,[z114,z0,z1,z2,z4,z5,z130]),(0,[z0,z1,z2,z4,z5,z298,z6])],[(0,[z0,z1,z2,z4,z5,z703,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z86,z1,z2,z4,z5,z38])],[(1,[z0,z463,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z704,z5,z6]),(0,[z0,z1,z2,z4,z5,z705,z6]),(1,[z0,z1,z638,z4,z5,z6]),(0,[z0,z1,z2,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z4,z707,z6]),(0,[z0,z1,z2,z4,z708,z6])],[(0,[z0,z1,z232,z4,z280,z6]),(0,[z0,z1,z2,z49,z53,z6])],[(0,[z709,z1,z2,z4,z5,z6]),(0,[z0,z710,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z139,z6]),(0,[z0,z28,z301,z4,z5,z6]),(0,[z0,z711,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z712]),(0,[z1,z2,z4,z135,z92,z6]),(0,[z114,z341,z2,z4,z5,z130]),(0,[z367,z1,z2,z49,z5,z6]),(0,[z0,z257,z1,z4,z37,z5])],[(0,[z134,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z304]),(0,[z0,z11,z2,z4,z105,z8]),(0,[z0,z713,z2,z4,z5,z6]),(0,[z671,z0,z2,z303,z5,z6]),(0,[z0,z1,z714,z55,z5,z6]),(0,[z0,z715,z2,z4,z5,z6])],[(0,[z0,z28,z150,z4,z5,z6]),(0,[z77,z0,z11,z55,z5,z6]),(0,[z0,z72,z371,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z716]),(0,[z717,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z718,z6]),(0,[z0,z1,z719,z4,z5,z6]),(0,[z0,z86,z4,z5,z206,z87]),(0,[z162,z0,z1,z4,z56,z6])],[(0,[z0,z72,z2,z4,z5,z409])],[(0,[z0,z28,z308,z4,z5,z6]),(0,[z0,z720,z2,z4,z5,z6]),(0,[z0,z1,z721,z4,z5,z6]),(0,[z0,z1,z2,z4,z722,z6]),(0,[z0,z1,z2,z4,z723,z6]),(0,[z0,z1,z2,z411,z53,z6]),(0,[z0,z1,z2,z4,z724,z6])]],
   [[(0,[z156,z725,z2,z4,z5,z6]),(0,[z0,z726,z2,z4,z5,z6])],[(0,[z0,z28,z102,z4,z5,z6]),(0,[z1,z2,z29,z727,z5,z6]),(0,[z0,z1,z232,z4,z607,z6]),(0,[z0,z1,z728,z2,z4,z5]),(0,[z0,z729,z2,z4,z5,z6]),(0,[z0,z1,z2,z49,z730,z6]),(0,[z0,z1,z731,z4,z5,z6])],[(0,[z11,z28,z2,z4,z5,z6]),(0,[z0,z1,z85,z4,z5,z130]),(0,[z0,z1,z4,z655,z5,z129]),(0,[z0,z1,z4,z8,z294,z5])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z0,z1,z24,z4,z5,z6])],[(0,[z475,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z733,z6]),(0,[z734,z1,z2,z4,z5,z6])],[(0,[z0,z11,z528,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z735]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z0,z257,z1,z4,z5,z52])],[(0,[z0,z709,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z92,z21]),(0,[z0,z1,z737,z4,z5,z6]),(0,[z0,z43,z1,z4,z5,z505])],[(0,[z0,z11,z18,z17,z5,z6]),(0,[z71,z1,z2,z4,z62,z6]),(0,[z0,z1,z2,z49,z633,z6]),(0,[z0,z124,z1,z4,z233,z5]),(0,[z0,z1,z4,z189,z56,z6]),(0,[z0,z1,z4,z37,z294,z38])]],
   [[(0,[z0,z28,z2,z44,z5,z148]),(0,[z0,z109,z2,z93,z5,z6]),(0,[z0,z1,z2,z4,z738,z6]),(0,[z115,z0,z683,z4,z5,z6]),(0,[z466,z2,z4,z135,z5,z6]),(0,[z0,z1,z739,z4,z5,z6]),(0,[z0,z1,z4,z714,z5,z6]),(0,[z0,z1,z2,z4,z724,z37])],[(0,[z211,z404,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z740,z6]),(0,[z27,z463,z2,z29,z5,z6]),(0,[z0,z1,z741,z4,z5,z6])],[(0,[z28,z390,z2,z4,z5,z6]),(0,[z0,z218,z28,z2,z4,z5]),(0,[z103,z28,z2,z4,z5,z6]),(0,[z0,z1,z742,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z743]),(0,[z0,z1,z2,z4,z5,z744]),(0,[z0,z43,z1,z4,z189,z5]),(0,[z0,z1,z4,z5,z6,z745]),(0,[z0,z1,z2,z4,z107,z8])],[(0,[z39,z28,z2,z4,z5,z6]),(0,[z28,z2,z4,z394,z5,z6]),(0,[z0,z1,z2,z4,z746,z6]),(1,[z1,z2,z4,z5,z747]),(0,[z0,z1,z4,z5,z206,z6]),(0,[z0,z748,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z749,z5])],[(0,[z0,z218,z1,z2,z4,z5]),(0,[z64,z0,z2,z303,z5,z442]),(0,[z0,z43,z1,z4,z5,z304])],[(0,[z0,z1,z2,z4,z5,z750]),(0,[z0,z1,z2,z751,z5,z6]),(0,[z0,z69,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z752,z6]),(0,[z23,z156,z1,z2,z41,z6])],[(0,[z0,z28,z753,z4,z5,z6]),(0,[z0,z1,z150,z4,z5,z442]),(0,[z0,z1,z2,z4,z754,z6]),(0,[z0,z1,z2,z5,z755,z52])],[(0,[z0,z756,z2,z4,z5,z6]),(0,[z28,z2,z4,z400,z5,z6]),(0,[z440,z0,z2,z250,z5,z6]),(0,[z0,z1,z2,z4,z5,z631]),(0,[z0,z757,z2,z4,z5,z6]),(0,[z0,z758,z116,z4,z5,z6])]],
   [[(0,[z0,z759,z2,z4,z5,z6]),(0,[z0,z1,z760,z4,z5,z6])],[(0,[z0,z192,z2,z4,z5,z6]),(0,[z162,z0,z11,z4,z56,z6]),(0,[z369,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z761]),(0,[z0,z124,z253,z4,z5,z6]),(0,[z0,z1,z24,z4,z5,z215]),(0,[z0,z1,z2,z4,z5,z215])],[(0,[z0,z1,z762,z4,z5,z6]),(0,[z0,z1,z4,z763,z5,z6]),(0,[z0,z1,z2,z4,z5,z764]),(0,[z765,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z172,z6,z104])],[(0,[z0,z43,z1,z4,z5,z745])],[(0,[z0,z28,z2,z4,z5,z766]),(0,[z0,z528,z28,z4,z5,z6]),(0,[z0,z72,z2,z4,z5,z14]),(0,[z13,z1,z308,z4,z62,z6]),(0,[z73,z1,z2,z4,z767,z6]),(0,[z768,z1,z2,z4,z5,z6]),(0,[z0,z769,z2,z4,z5,z6])],[(0,[z0,z11,z4,z292,z5,z6]),(0,[z0,z770,z2,z4,z5,z6]),(0,[z0,z1,z771,z4,z5,z6]),(0,[z0,z772,z1,z4,z5,z6]),(0,[z500,z1,z150,z4,z5,z6]),(0,[z126,z0,z2,z4,z137,z6]),(0,[z0,z69,z2,z4,z41,z6])],[(0,[z28,z2,z4,z248,z5,z6]),(0,[z0,z124,z376,z4,z5,z6]),(0,[z0,z1,z2,z4,z773,z6]),(0,[z0,z1,z25,z4,z5,z631]),(0,[z13,z1,z2,z4,z767,z6]),(0,[z0,z1,z2,z4,z767,z6]),(0,[z0,z43,z1,z4,z5,z540])],[(0,[z0,z774,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z775]),(0,[z630,z1,z2,z4,z5,z130]),(0,[z0,z1,z2,z4,z5,z231])]],
   [[(0,[z28,z2,z4,z256,z5,z6]),(0,[z0,z11,z2,z4,z5,z298]),(0,[z0,z1,z2,z4,z776,z5]),(0,[z306,z0,z1,z4,z56,z6]),(0,[z0,z1,z308,z195,z5,z6]),(0,[z0,z1,z777,z4,z5,z6]),(0,[z0,z778,z2,z4,z5,z6])],[(0,[z0,z1,z4,z779,z5,z6]),(0,[z0,z1,z85,z4,z5,z74]),(0,[z0,z83,z758,z4,z5,z6]),(0,[z500,z1,z102,z4,z5,z6]),(0,[z0,z1,z4,z780,z5,z6])],[(0,[z28,z2,z135,z5,z41,z6]),(0,[z0,z1,z308,z34,z5,z6]),(0,[z0,z1,z4,z55,z5,z231]),(0,[z0,z672,z1,z4,z5,z204]),(0,[z0,z781,z2,z4,z5,z6]),(0,[z0,z782,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z57,z8])],[(0,[z13,z11,z2,z4,z62,z6]),(0,[z455,z1,z2,z4,z62,z6]),(0,[z0,z1,z4,z5,z6,z783]),(0,[z384,z0,z83,z4,z5,z6]),(0,[z0,z69,z2,z4,z5,z215])],[(0,[z0,z28,z2,z4,z92,z6]),(0,[z0,z28,z4,z5,z784,z6]),(0,[z0,z785,z2,z4,z5,z6]),(0,[z0,z1,z2,z34,z61,z6]),(0,[z200,z0,z1,z2,z5,z52])],[(0,[z0,z1,z2,z4,z786,z5]),(0,[z0,z11,z4,z5,z6,z457]),(0,[z0,z43,z1,z4,z5,z690]),(0,[z391,z2,z4,z117,z5,z6]),(0,[z0,z1,z2,z4,z5,z787]),(0,[z0,z1,z2,z4,z788,z6]),(0,[z0,z1,z232,z4,z172,z6])],[(0,[z0,z1,z789,z4,z5,z6]),(0,[z0,z463,z2,z4,z5,z6]),(0,[z28,z2,z4,z5,z276,z6]),(0,[z361,z463,z2,z4,z5,z6]),(0,[z500,z11,z2,z4,z5,z6]),(0,[z0,z1,z638,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z790]),(0,[z0,z1,z2,z4,z189,z38])],[(0,[z0,z11,z2,z195,z5,z6]),(0,[z156,z1,z2,z4,z5,z6]),(0,[z0,z791,z2,z4,z5,z6]),(0,[z0,z792,z2,z4,z5,z6]),(0,[z0,z1,z2,z793,z5,z6]),(0,[z0,z2,z4,z550,z36,z6]),(0,[z156,z1,z24,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z794,z6]),(0,[z582,z28,z2,z4,z5,z6]),(0,[z0,z1,z284,z4,z5,z6]),(0,[z23,z0,z1,z24,z41,z6])],[(0,[z66,z0,z2,z4,z5,z40]),(0,[z0,z11,z2,z34,z5,z6]),(0,[z522,z0,z1,z55,z5,z6]),(0,[z1,z2,z4,z61,z767,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z0,z797,z2,z4,z5,z6]),(0,[z0,z798,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z105,z595])],[(0,[z0,z28,z799,z4,z5,z6]),(0,[z0,z800,z2,z4,z5,z6]),(0,[z64,z0,z2,z550,z5,z6]),(0,[z0,z1,z4,z801,z5,z6]),(0,[z0,z1,z4,z294,z5,z38])],[(0,[z0,z1,z2,z4,z5,z802]),(0,[z1,z2,z4,z5,z767,z6]),(0,[z391,z1,z2,z4,z5,z442]),(0,[z0,z1,z2,z4,z5,z803])],[(0,[z0,z28,z18,z17,z5,z6]),(0,[z0,z1,z804,z4,z5,z6]),(0,[z0,z1,z2,z4,z180,z38]),(0,[z0,z1,z805,z4,z5,z6])],[(0,[z0,z43,z1,z4,z5,z574])],[(0,[z0,z124,z131,z116,z4,z5]),(0,[z0,z1,z2,z4,z5,z806]),(0,[z0,z2,z4,z807,z5,z6]),(0,[z126,z0,z2,z4,z736,z6]),(0,[z0,z1,z18,z4,z233,z5])],[(0,[z0,z28,z2,z4,z37,z38]),(0,[z0,z11,z808,z4,z5,z6]),(0,[z11,z613,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z809]),(0,[z0,z372,z287,z4,z5,z6]),(0,[z0,z1,z301,z4,z5,z6]),(0,[z0,z26,z2,z93,z5,z6]),(0,[z0,z810,z1,z4,z5,z6]),(0,[z96,z0,z528,z1,z4,z5])]],
   [[(0,[z0,z1,z811,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z214]),(0,[z0,z69,z638,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z353]),(0,[z0,z812,z2,z4,z5,z6])],[(0,[z0,z72,z2,z4,z5,z6]),(0,[z0,z26,z2,z553,z5,z6])],[(0,[z28,z2,z4,z5,z468,z6]),(0,[z0,z1,z2,z4,z5,z813]),(0,[z0,z1,z142,z4,z138,z6]),(0,[z0,z814,z2,z4,z5,z6]),(0,[z0,z1,z815,z4,z5,z6]),(0,[z0,z1,z4,z816,z5,z6]),(0,[z0,z1,z374,z4,z5,z148])],[(0,[z211,z11,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z817,z5]),(0,[z77,z0,z1,z55,z5,z6]),(0,[z367,z1,z2,z4,z53,z6]),(0,[z0,z1,z638,z4,z5,z215])],[(0,[z0,z1,z818,z4,z5,z6]),(0,[z0,z1,z4,z5,z819,z6]),(0,[z156,z1,z2,z4,z5,z215]),(0,[z0,z1,z2,z591,z5,z148]),(0,[z0,z820,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z821]),(0,[z0,z822,z2,z4,z5,z6]),(0,[z823,z1,z2,z4,z5,z6])],[(0,[z0,z1,z824,z4,z5,z6])]],
   [[(0,[z28,z482,z2,z4,z5,z6]),(0,[z825,z0,z2,z4,z5,z6]),(0,[z0,z1,z826,z4,z5,z6]),(0,[z1,z2,z4,z5,z130,z747]),(0,[z827,z1,z2,z4,z5,z6]),(0,[z0,z1,z828,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z829]),(0,[z0,z830,z2,z4,z5,z6]),(0,[z0,z11,z831,z4,z5,z6]),(0,[z1,z2,z4,z5,z747,z74]),(0,[z0,z1,z2,z4,z5,z832]),(0,[z0,z833,z1,z2,z4,z5])],[(0,[z11,z709,z2,z4,z5,z6]),(0,[z0,z834,z2,z4,z5,z6]),(0,[z162,z0,z1,z4,z551,z6]),(0,[z0,z1,z470,z4,z5,z129]),(0,[z23,z0,z1,z2,z730,z6])],[(0,[z0,z1,z835,z4,z5,z6]),(0,[z0,z1,z836,z4,z5,z6]),(0,[z0,z86,z2,z4,z5,z837]),(0,[z0,z1,z128,z4,z294,z5]),(0,[z23,z0,z69,z2,z41,z6])],[(0,[z0,z838,z2,z4,z5,z6]),(0,[z669,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z442]),(0,[z0,z1,z2,z392,z5,z52]),(0,[z367,z324,z2,z4,z5,z6])],[(0,[z0,z28,z287,z4,z5,z6]),(0,[z27,z1,z2,z4,z92,z6]),(0,[z0,z84,z119,z4,z5,z6]),(0,[z0,z1,z119,z4,z138,z6]),(0,[z73,z199,z2,z4,z61,z6]),(0,[z0,z1,z839,z4,z5,z6]),(1,[z0,z2,z4,z5,z837]),(0,[z0,z1,z2,z4,z840,z5])],[(0,[z32,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z265]),(0,[z0,z841,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z842]),(0,[z0,z1,z131,z2,z4,z5]),(0,[z64,z0,z2,z843,z5,z6]),(0,[z0,z43,z1,z523,z4,z5])],[(0,[z0,z310,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z844,z6]),(0,[z0,z1,z2,z845,z5,z6]),(0,[z367,z1,z2,z4,z5,z265]),(0,[z0,z846,z2,z4,z5,z6])]],
   [[(0,[z20,z84,z2,z135,z5,z6]),(0,[z20,z1,z2,z135,z138,z6])],[(0,[z0,z1,z2,z4,z5,z847]),(0,[z20,z1,z142,z135,z5,z6]),(0,[z1,z2,z727,z135,z5,z6]),(0,[z0,z848,z2,z4,z5,z6]),(0,[z0,z599,z2,z4,z5,z87]),(0,[z849,z1,z2,z4,z5,z6])],[(0,[z0,z28,z4,z5,z6,z457]),(0,[z0,z11,z2,z4,z5,z850]),(0,[z0,z851,z2,z4,z5,z6]),(0,[z0,z218,z124,z116,z4,z5]),(0,[z115,z0,z4,z5,z6,z323]),(0,[z852,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z853]),(0,[z156,z1,z638,z4,z5,z6]),(0,[z0,z854,z2,z4,z5,z6])],[(0,[z39,z709,z2,z4,z5,z6]),(0,[z0,z28,z4,z294,z5,z6]),(0,[z500,z28,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z855,z6]),(0,[z0,z84,z2,z4,z92,z6]),(0,[z123,z163,z2,z4,z5,z74]),(0,[z0,z856,z1,z4,z5,z6])],[(0,[z0,z857,z2,z4,z5,z6]),(0,[z0,z1,z858,z4,z5,z6]),(0,[z317,z0,z2,z4,z36,z6])],[(0,[z28,z2,z4,z135,z5,z6]),(0,[z0,z1,z2,z4,z5,z859]),(0,[z0,z1,z2,z4,z860,z5]),(0,[z0,z1,z2,z4,z5,z861]),(0,[z0,z1,z2,z4,z5,z862]),(0,[z114,z1,z85,z4,z5,z130]),(0,[z0,z1,z863,z4,z5,z6]),(0,[z23,z0,z1,z2,z41,z265])],[(0,[z162,z0,z28,z4,z56,z6]),(0,[z383,z11,z2,z4,z5,z6])],[(0,[z28,z2,z4,z5,z356,z6]),(0,[z0,z11,z2,z4,z5,z631]),(0,[z446,z0,z2,z4,z185,z6]),(0,[z0,z864,z2,z4,z5,z6]),(0,[z0,z124,z758,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z865]),(0,[z115,z0,z1,z4,z233,z5]),(0,[z0,z1,z2,z4,z5,z866]),(0,[z0,z2,z93,z5,z144,z6])]],
   [[(0,[z252,z28,z2,z4,z5,z6]),(0,[z0,z867,z2,z4,z5,z6]),(0,[z868,z0,z2,z4,z5,z6]),(0,[z869,z1,z2,z4,z5,z6]),(0,[z0,z1,z870,z4,z5,z6])],[(0,[z123,z28,z2,z4,z5,z74]),(0,[z0,z1,z2,z4,z5,z766]),(0,[z0,z1,z871,z4,z5,z6]),(0,[z0,z872,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z873]),(0,[z58,z0,z1,z2,z5,z52])],[(0,[z0,z11,z762,z4,z5,z6])],[(0,[z190,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z438,z5]),(0,[z0,z1,z119,z4,z5,z6]),(0,[z0,z1,z147,z4,z5,z631]),(0,[z0,z1,z2,z4,z874,z6]),(0,[z0,z875,z2,z4,z5,z6]),(0,[z0,z1,z308,z4,z5,z409]),(0,[z0,z876,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z105,z724])],[(0,[z0,z1,z374,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z214]),(0,[z0,z90,z2,z553,z5,z6]),(0,[z27,z1,z2,z258,z5,z6]),(0,[z0,z1,z4,z5,z56,z304]),(0,[z0,z257,z1,z4,z5,z148])],[(0,[z0,z309,z2,z4,z5,z87]),(0,[z0,z11,z2,z4,z773,z6]),(0,[z20,z1,z2,z135,z5,z6]),(0,[z0,z877,z2,z4,z5,z6]),(0,[z0,z1,z18,z17,z5,z214]),(0,[z0,z43,z1,z4,z5,z644])],[(0,[z0,z11,z2,z4,z5,z231]),(0,[z0,z1,z4,z5,z878,z6])]],
   [[(0,[z0,z11,z2,z4,z776,z5]),(0,[z0,z879,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z747]),(0,[z0,z1,z880,z4,z5,z6]),(0,[z0,z1,z2,z4,z881,z6]),(0,[z0,z1,z4,z37,z457,z38])],[(0,[z211,z28,z147,z4,z5,z6]),(0,[z0,z1,z4,z5,z784,z6]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z361,z709,z2,z4,z5,z6]),(0,[z0,z11,z371,z4,z5,z6]),(0,[z115,z0,z4,z5,z364,z6])],[(0,[z367,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z409]),(0,[z590,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z883]),(0,[z0,z1,z2,z4,z5,z884]),(0,[z885,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z886]),(0,[z0,z86,z253,z2,z4,z5]),(0,[z162,z0,z1,z4,z65,z56])],[(0,[z278,z0,z88,z4,z5,z6]),(0,[z0,z1,z887,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z888]),(0,[z0,z1,z889,z4,z5,z6]),(0,[z0,z341,z287,z4,z5,z6]),(0,[z0,z890,z2,z4,z5,z6])],[(0,[z96,z0,z2,z4,z5,z531]),(0,[z500,z1,z2,z4,z5,z442]),(0,[z0,z1,z891,z4,z5,z6])],[(0,[z0,z109,z2,z3,z5,z6]),(0,[z0,z424,z2,z4,z138,z6]),(0,[z0,z26,z2,z4,z137,z6]),(0,[z0,z892,z1,z4,z5,z6]),(1,[z367,z1,z2,z41,z6])],[(0,[z0,z28,z4,z5,z351,z6]),(0,[z0,z1,z2,z4,z5,z893]),(0,[z0,z424,z142,z4,z5,z6]),(0,[z0,z2,z843,z303,z5,z6]),(0,[z894,z1,z2,z4,z5,z6]),(0,[z367,z1,z2,z5,z41,z6]),(0,[z23,z0,z324,z2,z41,z6]),(0,[z0,z1,z2,z4,z5,z755])],[(0,[z0,z199,z2,z4,z5,z6]),(0,[z0,z1,z799,z4,z5,z6]),(0,[z126,z0,z2,z4,z185,z6]),(0,[z0,z1,z128,z4,z5,z129])]],
   [[(0,[z0,z28,z2,z4,z5,z21]),(0,[z0,z895,z2,z4,z5,z6]),(0,[z0,z1,z2,z54,z53,z6]),(0,[z0,z1,z4,z896,z5,z6]),(0,[z0,z897,z2,z4,z5,z6]),(0,[z0,z69,z24,z4,z5,z6])],[(0,[z0,z2,z4,z5,z898,z6]),(0,[z0,z899,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z900,z5])],[(0,[z0,z1,z2,z4,z5,z901]),(0,[z0,z1,z902,z4,z5,z6]),(0,[z0,z1,z4,z903,z5,z6])],[(0,[z0,z404,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z265]),(0,[z222,z28,z2,z4,z5,z6]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z905]),(0,[z906,z1,z2,z4,z5,z6]),(0,[z0,z1,z907,z4,z5,z6]),(0,[z0,z1,z4,z908,z5,z6])],[(0,[z0,z22,z308,z4,z5,z6]),(0,[z0,z1,z2,z4,z233,z5]),(0,[z0,z43,z1,z4,z5,z204]),(0,[z0,z909,z2,z4,z5,z6])],[(0,[z391,z28,z2,z4,z5,z6]),(0,[z114,z1,z2,z4,z5,z130])],[(0,[z0,z11,z218,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z353]),(0,[z0,z910,z2,z4,z5,z6]),(0,[z0,z911,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z912,z6]),(0,[z0,z1,z4,z5,z913,z6]),(0,[z0,z1,z4,z55,z233,z5])]],
   [[(0,[z28,z2,z49,z135,z5,z6]),(0,[z395,z28,z2,z4,z5,z6]),(0,[z0,z11,z914,z4,z5,z6]),(0,[z0,z1,z915,z4,z5,z6]),(0,[z0,z1,z916,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z917]),(0,[z0,z918,z2,z4,z5,z6])],[(0,[z759,z28,z2,z4,z5,z6]),(0,[z0,z84,z2,z4,z5,z293]),(0,[z0,z1,z2,z4,z138,z293]),(0,[z0,z1,z308,z4,z5,z14]),(1,[z1,z2,z34,z62,z6]),(0,[z0,z1,z919,z4,z5,z6]),(0,[z0,z1,z2,z4,z139,z125]),(0,[z0,z1,z920,z4,z5,z6]),(0,[z96,z0,z2,z4,z5,z51])],[(0,[z463,z28,z2,z4,z5,z6]),(0,[z66,z0,z2,z4,z5,z51]),(0,[z0,z11,z2,z4,z65,z5]),(0,[z0,z1,z142,z4,z5,z293]),(0,[z64,z0,z2,z303,z5,z125]),(0,[z0,z1,z2,z4,z5,z921]),(0,[z23,z367,z1,z2,z41,z6]),(0,[z0,z922,z2,z4,z5,z6])],[(0,[z0,z424,z2,z4,z5,z6]),(0,[z0,z1,z25,z4,z233,z5]),(0,[z0,z1,z2,z4,z923,z5])],[(0,[z0,z1,z2,z4,z5,z924]),(0,[z0,z28,z2,z4,z105,z8]),(0,[z73,z11,z2,z4,z61,z6]),(0,[z0,z1,z4,z5,z129,z398]),(0,[z0,z1,z150,z4,z5,z125]),(0,[z64,z0,z2,z303,z137,z6])],[(0,[z0,z925,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z926]),(0,[z573,z28,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z927,z6]),(0,[z0,z11,z85,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z928]),(0,[z0,z929,z2,z4,z5,z6]),(0,[z0,z1,z150,z4,z137,z6]),(0,[z0,z257,z1,z4,z5,z6])],[(0,[z0,z380,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z930,z6]),(0,[z0,z931,z2,z4,z5,z6]),(0,[z580,z1,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z932,z6]),(0,[z0,z1,z2,z4,z5,z118]),(0,[z0,z43,z1,z4,z5,z688]),(0,[z0,z933,z2,z4,z5,z6])]],
   [[(0,[z0,z28,z2,z4,z438,z5]),(0,[z0,z11,z2,z4,z5,z14]),(0,[z0,z11,z826,z4,z5,z6]),(0,[z391,z2,z4,z303,z5,z6]),(0,[z0,z1,z102,z4,z5,z125]),(0,[z0,z1,z934,z4,z5,z6]),(0,[z0,z257,z1,z4,z5,z129]),(0,[z0,z1,z44,z292,z5,z148])],[(0,[z27,z11,z2,z29,z5,z6]),(0,[z0,z935,z2,z4,z5,z6]),(0,[z0,z349,z116,z4,z5,z6])],[(0,[z421,z1,z2,z135,z5,z6]),(0,[z0,z936,z2,z4,z5,z6]),(0,[z27,z1,z2,z727,z5,z6]),(0,[z0,z1,z102,z4,z137,z6])],[(0,[z28,z2,z4,z5,z445,z6]),(1,[z0,z1,z4,z5,z745]),(0,[z0,z1,z937,z4,z5,z6])],[],[(0,[z0,z1,z4,z938,z5,z6]),(0,[z0,z11,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z5,z939]),(0,[z96,z0,z2,z415,z4,z5])],[(0,[z0,z28,z371,z4,z5,z6]),(0,[z0,z97,z376,z4,z5,z6]),(0,[z140,z11,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z940]),(0,[z126,z391,z2,z4,z5,z6]),(0,[z162,z0,z1,z4,z56,z304]),(0,[z0,z941,z2,z4,z5,z6]),(0,[z0,z1,z128,z4,z239,z5])],[(0,[z64,z0,z2,z250,z5,z6]),(0,[z0,z11,z2,z4,z137,z6]),(0,[z0,z1,z2,z4,z5,z293]),(0,[z0,z1,z2,z4,z5,z942]),(1,[z0,z2,z843,z5,z6]),(0,[z0,z1,z943,z4,z5,z6])]],
   [[(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z11,z2,z4,z138,z6]),(0,[z0,z1,z2,z4,z5,z945]),(0,[z0,z1,z2,z4,z5,z946]),(0,[z220,z0,z2,z4,z137,z6]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z0,z1,z4,z5,z745,z204]),(0,[z367,z947,z2,z4,z5,z6])],[(0,[z610,z28,z2,z4,z5,z6]),(0,[z0,z11,z142,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z948])],[(0,[z0,z28,z2,z4,z5,z949]),(0,[z9,z0,z2,z303,z5,z6]),(0,[z0,z1,z2,z4,z5,z950]),(0,[z64,z391,z2,z303,z5,z6]),(0,[z0,z1,z2,z4,z139,z6]),(0,[z0,z1,z128,z4,z5,z448])],[(0,[z0,z28,z2,z4,z951,z5]),(0,[z0,z1,z2,z4,z952,z6]),(0,[z0,z380,z2,z4,z5,z631]),(0,[z0,z1,z2,z4,z953,z5]),(0,[z64,z0,z2,z303,z5,z6])],[(0,[z167,z0,z2,z4,z89,z6]),(0,[z0,z11,z2,z49,z53,z6]),(0,[z0,z1,z4,z5,z954,z6]),(0,[z0,z1,z2,z955,z5,z6]),(0,[z0,z1,z2,z4,z273,z38]),(0,[z0,z1,z2,z4,z5,z304]),(0,[z156,z69,z2,z4,z5,z6])],[(0,[z77,z0,z28,z55,z5,z6]),(0,[z0,z956,z1,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z859]),(0,[z0,z372,z85,z4,z5,z6]),(0,[z0,z1,z150,z4,z5,z6]),(0,[z115,z0,z218,z1,z4,z5])],[(0,[z0,z1,z2,z4,z5,z957]),(0,[z0,z958,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z959]),(0,[z0,z960,z2,z4,z5,z6])],[(0,[z11,z378,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z961]),(0,[z0,z1,z308,z4,z5,z6]),(0,[z0,z84,z2,z4,z5,z21]),(0,[z962,z1,z2,z4,z5,z6])]],
   [[(0,[z389,z0,z1,z55,z5,z6]),(0,[z23,z220,z0,z2,z41,z6])],[(0,[z0,z1,z2,z4,z5,z963]),(0,[z84,z2,z4,z135,z5,z6]),(0,[z0,z1,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z964,z6]),(0,[z391,z1,z2,z4,z5,z125])],[(0,[z965,z1,z2,z4,z5,z6])],[(0,[z0,z1,z4,z5,z966,z6]),(0,[z0,z967,z2,z4,z5,z6]),(0,[z0,z1,z968,z4,z5,z6]),(0,[z0,z1,z969,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z970]),(0,[z391,z1,z2,z4,z137,z6]),(0,[z0,z1,z2,z4,z5,z745])],[(0,[z0,z309,z2,z4,z5,z340]),(0,[z307,z28,z2,z4,z5,z6]),(0,[z0,z971,z2,z4,z5,z6]),(0,[z0,z1,z972,z4,z5,z6])],[(0,[z0,z28,z4,z292,z5,z6]),(0,[z0,z1,z2,z4,z5,z973]),(0,[z0,z1,z4,z438,z5,z351])],[(0,[z0,z11,z2,z4,z5,z6]),(0,[z361,z11,z2,z4,z5,z6]),(0,[z0,z11,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z974]),(0,[z0,z1,z2,z4,z5,z975]),(0,[z0,z2,z4,z5,z467,z6]),(0,[z0,z976,z1,z4,z5,z6]),(0,[z1,z2,z4,z5,z977,z6]),(0,[z0,z1,z2,z4,z724,z38])],[(0,[z0,z28,z2,z4,z65,z5]),(0,[z367,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z115,z0,z758,z4,z5,z6]),(0,[z220,z0,z2,z4,z5,z6]),(0,[z0,z979,z2,z4,z5,z6]),(0,[z0,z980,z2,z4,z5,z6]),(0,[z0,z257,z1,z4,z105,z5])]],
   [[(0,[z0,z28,z2,z4,z981,z6]),(0,[z0,z28,z2,z4,z5,z298]),(0,[z0,z982,z2,z4,z5,z6]),(0,[z0,z1,z2,z44,z5,z148])],[(0,[z0,z45,z2,z4,z5,z353]),(0,[z0,z43,z1,z4,z5,z91]),(0,[z0,z1,z2,z345,z5,z148])],[(0,[z0,z1,z2,z4,z983,z5]),(0,[z0,z528,z1,z4,z5,z52]),(0,[z0,z1,z2,z4,z984,z6])],[(0,[z13,z28,z2,z4,z62,z6]),(0,[z430,z11,z2,z4,z5,z6]),(0,[z13,z1,z371,z4,z62,z6]),(0,[z0,z1,z4,z5,z351,z6]),(0,[z0,z1,z985,z4,z5,z6])],[(1,[z1,z2,z727,z5,z6]),(0,[z0,z1,z2,z4,z5,z986]),(0,[z0,z1,z4,z233,z5,z204])],[(0,[z0,z28,z2,z4,z5,z14]),(0,[z0,z1,z2,z4,z5,z21]),(0,[z0,z1,z4,z987,z5,z6]),(0,[z0,z1,z988,z4,z5,z6]),(0,[z23,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z730,z6]),(0,[z79,z0,z1,z2,z5,z755])],[(0,[z0,z1,z753,z4,z5,z6]),(0,[z0,z1,z989,z2,z4,z5]),(0,[z0,z11,z4,z5,z206,z6]),(0,[z990,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z148,z755]),(0,[z0,z1,z991,z4,z5,z6])],[(0,[z27,z28,z2,z4,z5,z6]),(0,[z0,z28,z2,z195,z5,z6]),(0,[z0,z28,z2,z4,z992,z6]),(0,[z0,z458,z2,z4,z5,z518]),(0,[z0,z11,z128,z4,z5,z129]),(0,[z0,z1,z2,z4,z993,z5]),(0,[z0,z1,z142,z4,z92,z6]),(0,[z1,z2,z135,z62,z41,z6]),(0,[z0,z1,z371,z195,z5,z6]),(0,[z0,z1,z2,z4,z5,z994]),(0,[z995,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z402]),(0,[z0,z1,z4,z5,z551,z204]),(0,[z367,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z724,z5])]],
   [[(1,[z1,z2,z135,z92,z6]),(0,[z0,z1,z2,z195,z5,z409]),(0,[z0,z1,z2,z687,z5,z148]),(0,[z96,z0,z2,z4,z5,z837]),(0,[z0,z324,z2,z4,z5,z265]),(0,[z0,z1,z2,z4,z8,z724])],[(0,[z0,z28,z2,z34,z5,z6]),(0,[z278,z0,z83,z4,z5,z6]),(0,[z0,z996,z2,z4,z5,z6]),(0,[z0,z1,z997,z4,z5,z6]),(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z1,z999,z4,z5,z6]),(0,[z0,z1000,z2,z4,z5,z6]),(0,[z0,z1,z371,z34,z5,z6]),(0,[z0,z1,z4,z1001,z5,z6]),(0,[z1002,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1003,z5,z6]),(0,[z0,z1,z2,z4,z1004,z5]),(0,[z0,z1,z2,z4,z5,z1005]),(0,[z0,z2,z4,z5,z1006,z6]),(0,[z0,z1,z2,z4,z5,z1007]),(0,[z0,z1,z1008,z4,z5,z6])],[(0,[z391,z1,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z125]),(0,[z0,z11,z902,z4,z5,z6]),(0,[z0,z1,z1009,z4,z5,z6]),(0,[z0,z124,z116,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1010]),(0,[z0,z257,z86,z1,z4,z5])],[(0,[z90,z28,z2,z4,z5,z6]),(0,[z545,z0,z683,z4,z5,z6]),(0,[z0,z11,z760,z4,z5,z6]),(0,[z0,z1011,z2,z4,z5,z6]),(0,[z114,z1,z2,z4,z5,z747]),(0,[z0,z1,z301,z4,z5,z118]),(0,[z0,z1,z2,z4,z37,z551])],[(0,[z0,z28,z2,z4,z137,z6]),(0,[z0,z11,z2,z4,z233,z5]),(0,[z0,z1012,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z215]),(0,[z0,z1,z2,z4,z1013,z6]),(0,[z0,z1,z2,z4,z5,z1014]),(0,[z0,z1,z4,z521,z56,z6]),(0,[z0,z86,z528,z4,z5,z87])],[(0,[z0,z372,z2,z4,z5,z6]),(0,[z0,z1015,z1,z2,z4,z5]),(0,[z114,z11,z2,z4,z5,z130]),(0,[z1016,z1,z2,z4,z5,z6]),(0,[z367,z1,z2,z4,z5,z215]),(0,[z0,z1017,z1,z4,z5,z6]),(0,[z0,z1,z1018,z4,z5,z6])],[(0,[z95,z11,z2,z4,z5,z6]),(0,[z20,z1,z119,z135,z5,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z1020,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z233,z172,z5]),(0,[z0,z1021,z2,z4,z5,z6]),(0,[z0,z1022,z2,z4,z5,z6])],[(0,[z187,z0,z43,z1,z4,z5]),(0,[z0,z1,z2,z4,z5,z1023])]],
   [[(0,[z0,z1,z147,z4,z233,z5]),(0,[z20,z1,z2,z727,z5,z6]),(0,[z1024,z0,z2,z4,z5,z6]),(0,[z115,z0,z83,z4,z5,z6]),(0,[z0,z218,z1,z18,z4,z5]),(0,[z0,z1025,z2,z4,z5,z6]),(0,[z0,z1,z4,z1026,z5,z6]),(0,[z0,z1027,z2,z4,z5,z6])],[(0,[z0,z1,z119,z4,z92,z6]),(0,[z0,z1,z2,z4,z5,z1028])],[(0,[z709,z28,z2,z4,z5,z6]),(0,[z425,z28,z2,z4,z5,z6]),(0,[z216,z0,z2,z4,z5,z531]),(0,[z0,z1,z1029,z4,z5,z6]),(0,[z0,z367,z1,z2,z41,z6])],[(0,[z0,z11,z43,z4,z5,z204]),(0,[z0,z1,z1030,z4,z5,z6]),(0,[z23,z0,z1,z2,z41,z215])],[(0,[z0,z1,z2,z4,z5,z1031]),(0,[z0,z1,z2,z4,z92,z6]),(0,[z0,z257,z1,z4,z5,z74]),(0,[z162,z0,z1,z4,z233,z5])],[(0,[z0,z163,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1032]),(0,[z0,z1033,z2,z4,z5,z6]),(0,[z13,z22,z2,z4,z62,z6]),(0,[z23,z0,z2,z467,z41,z6])],[(0,[z0,z1,z2,z4,z1034,z5]),(0,[z0,z1035,z2,z4,z5,z6]),(0,[z0,z1,z232,z4,z5,z304])],[(0,[z0,z1,z2,z4,z5,z1036]),(0,[z0,z11,z2,z4,z930,z6]),(0,[z0,z2,z4,z117,z137,z6]),(0,[z64,z0,z2,z303,z139,z6]),(0,[z0,z1,z2,z4,z5,z1037]),(0,[z0,z1,z401,z55,z5,z6]),(0,[z0,z1,z2,z5,z730,z6]),(0,[z0,z1,z4,z5,z6,z1038])]],
   [[(0,[z0,z11,z232,z4,z172,z6]),(0,[z0,z1,z2,z4,z5,z1039]),(0,[z0,z1,z128,z120,z4,z5]),(0,[z0,z43,z1,z4,z5,z184])],[(0,[z28,z2,z4,z250,z5,z6]),(0,[z0,z11,z638,z4,z5,z6]),(0,[z23,z0,z11,z2,z41,z6]),(0,[z1,z997,z2,z4,z5,z6]),(0,[z0,z22,z2,z195,z5,z6]),(0,[z0,z1,z150,z4,z139,z6]),(0,[z0,z2,z1040,z4,z5,z6]),(0,[z0,z1041,z2,z4,z5,z6])],[(0,[z156,z11,z2,z4,z5,z6]),(0,[z13,z1,z2,z4,z62,z14]),(0,[z0,z1,z18,z714,z5,z6]),(0,[z367,z1,z638,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z6]),(0,[z0,z28,z24,z4,z5,z6]),(0,[z0,z11,z284,z4,z5,z6]),(0,[z0,z22,z2,z34,z5,z6]),(0,[z0,z1,z2,z1042,z5,z6]),(0,[z1043,z1,z2,z4,z5,z6]),(0,[z0,z1044,z2,z4,z5,z6]),(0,[z0,z1,z1045,z2,z4,z5]),(0,[z0,z2,z4,z5,z6,z1046]),(0,[z0,z1047,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1048]),(0,[z13,z1,z2,z195,z62,z6]),(0,[z0,z1,z18,z17,z5,z6]),(0,[z0,z1,z2,z4,z622,z38])],[(0,[z0,z43,z28,z4,z5,z204]),(0,[z0,z1,z2,z4,z1049,z5]),(0,[z0,z1,z4,z1050,z5,z6]),(0,[z0,z1,z4,z5,z6,z1051]),(0,[z0,z1,z102,z4,z139,z6]),(0,[z0,z1,z2,z4,z137,z442])],[(0,[z0,z914,z1,z4,z5,z6]),(0,[z0,z72,z308,z4,z5,z6]),(0,[z13,z1,z2,z34,z62,z6]),(0,[z0,z1,z2,z195,z5,z14]),(0,[z64,z0,z102,z303,z5,z6]),(0,[z156,z846,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1052,z5])],[(0,[z0,z11,z2,z4,z5,z293]),(0,[z0,z1,z2,z4,z5,z743]),(0,[z0,z1053,z1,z4,z5,z6]),(0,[z1054,z0,z2,z4,z5,z6]),(0,[z0,z1055,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z37,z38])]],
   [[(0,[z9,z28,z2,z135,z5,z6]),(0,[z0,z28,z2,z4,z738,z6]),(0,[z0,z1,z1056,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z945]),(0,[z0,z1,z2,z4,z5,z1057]),(0,[z0,z1058,z2,z4,z5,z6]),(0,[z0,z1,z2,z34,z5,z14]),(0,[z0,z1,z2,z4,z1059,z5]),(0,[z0,z1060,z2,z4,z5,z6])],[(0,[z0,z1,z1061,z4,z5,z6]),(0,[z0,z1,z1062,z4,z5,z6]),(0,[z0,z1,z2,z4,z1063,z5]),(0,[z0,z1,z1064,z4,z5,z6])],[(0,[z357,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z139,z6]),(0,[z0,z11,z301,z4,z5,z6]),(0,[z27,z466,z2,z4,z5,z6]),(0,[z0,z1,z1065,z4,z5,z6]),(0,[z0,z1066,z1,z2,z4,z5]),(0,[z500,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z5,z1067])],[(0,[z0,z28,z4,z5,z206,z6]),(0,[z0,z424,z119,z4,z5,z6])],[(0,[z0,z11,z2,z4,z5,z304]),(0,[z0,z218,z124,z1,z4,z5]),(0,[z500,z1,z2,z4,z137,z6]),(0,[z1068,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z1069,z5,z6])],[(0,[z0,z11,z150,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1070]),(0,[z0,z1,z1071,z4,z5,z6]),(0,[z348,z0,z1,z2,z5,z52]),(0,[z0,z2,z4,z736,z36,z6]),(0,[z0,z1,z2,z5,z6,z755])],[(0,[z333,z28,z2,z4,z5,z6]),(0,[z27,z84,z2,z4,z5,z6]),(0,[z20,z424,z2,z135,z5,z6]),(0,[z0,z1,z128,z4,z233,z5]),(0,[z0,z1,z232,z4,z512,z6])],[(0,[z0,z28,z2,z4,z5,z631]),(0,[z0,z257,z28,z4,z5,z6]),(0,[z0,z11,z308,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z961]),(0,[z0,z1072,z2,z4,z5,z6])]],
   [[(0,[z28,z2,z4,z5,z585,z6]),(0,[z0,z1073,z1,z2,z4,z5]),(0,[z1074,z1,z2,z4,z5,z6]),(0,[z0,z1075,z2,z4,z5,z6])],[(0,[z0,z1076,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z215]),(0,[z0,z1,z2,z4,z1077,z6]),(0,[z0,z11,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1078]),(0,[z0,z1,z1079,z4,z5,z6])],[(0,[z0,z11,z1080,z2,z4,z5]),(0,[z0,z1,z128,z4,z5,z157]),(0,[z0,z1,z4,z292,z5,z6])],[],[(0,[z0,z1,z2,z4,z5,z1081]),(0,[z0,z1,z2,z4,z5,z442]),(0,[z23,z0,z1,z638,z41,z6])],[(0,[z0,z1,z2,z4,z981,z6]),(0,[z0,z1,z287,z4,z5,z6]),(0,[z543,z1,z2,z4,z5,z130]),(0,[z0,z2,z4,z5,z6,z1082]),(0,[z367,z830,z2,z4,z5,z6]),(0,[z0,z1083,z2,z4,z5,z6])],[(0,[z0,z124,z262,z4,z5,z6]),(0,[z0,z1084,z2,z4,z5,z6]),(0,[z0,z1085,z2,z4,z5,z6]),(0,[z0,z1086,z1,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z231]),(0,[z0,z43,z1,z4,z5,z268]),(0,[z0,z1,z119,z4,z5,z293]),(0,[z455,z1,z2,z135,z5,z6]),(0,[z0,z1087,z2,z4,z5,z6])]],
   [[(0,[z0,z11,z2,z44,z5,z148]),(0,[z0,z1,z2,z4,z5,z1088]),(0,[z0,z1089,z2,z4,z5,z6]),(0,[z13,z1,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z5,z1090]),(0,[z0,z1,z18,z17,z5,z231]),(0,[z0,z1,z374,z4,z5,z52])],[(0,[z0,z11,z131,z2,z4,z5]),(0,[z0,z1,z2,z4,z1091,z5]),(0,[z1092,z1,z2,z4,z5,z6]),(0,[z0,z1093,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z409]),(0,[z79,z0,z11,z2,z5,z52]),(0,[z20,z1,z2,z135,z5,z293]),(0,[z0,z1,z371,z4,z5,z409]),(0,[z0,z1,z4,z5,z6,z457])],[(0,[z500,z1,z2,z4,z5,z6]),(0,[z126,z0,z2,z4,z36,z6]),(0,[z0,z1,z4,z294,z5,z6])],[(0,[z0,z1,z2,z4,z992,z6]),(0,[z0,z1,z2,z195,z5,z6]),(0,[z73,z1,z2,z34,z5,z6]),(0,[z0,z1094,z2,z4,z5,z6]),(0,[z0,z2,z4,z843,z5,z6]),(0,[z0,z1,z2,z730,z41,z6])],[(0,[z0,z28,z2,z4,z786,z5]),(0,[z0,z1,z2,z4,z92,z293]),(0,[z0,z1,z1095,z4,z5,z6]),(1,[z0,z1,z4,z984,z6]),(0,[z0,z1096,z2,z4,z5,z6])],[(0,[z0,z956,z28,z4,z5,z6]),(0,[z0,z28,z638,z4,z5,z6]),(0,[z0,z466,z2,z4,z5,z6]),(0,[z0,z11,z989,z2,z4,z5]),(0,[z575,z11,z2,z4,z5,z6]),(0,[z593,z1,z147,z4,z5,z6]),(0,[z0,z1,z612,z4,z5,z129]),(0,[z0,z1,z2,z1097,z5,z6]),(0,[z0,z1098,z2,z4,z5,z6]),(0,[z0,z1,z1099,z4,z5,z6])],[(0,[z0,z43,z701,z1,z4,z5])]],
   [[(0,[z27,z28,z2,z135,z5,z6]),(0,[z0,z28,z1100,z2,z4,z5]),(0,[z0,z28,z284,z4,z5,z6]),(1,[z0,z1,z714,z5,z6]),(0,[z0,z1,z18,z660,z5,z6]),(0,[z0,z1,z4,z5,z1101,z6])],[(0,[z387,z11,z2,z4,z5,z6]),(0,[z1102,z0,z1,z4,z5,z6]),(0,[z123,z1,z2,z4,z5,z74]),(0,[z0,z1,z2,z4,z5,z1103])],[(0,[z0,z380,z2,z4,z5,z353]),(0,[z0,z1104,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z138,z21]),(0,[z0,z1,z1105,z4,z5,z6]),(0,[z0,z1,z1106,z4,z5,z6]),(0,[z127,z1,z2,z4,z5,z130])],[(0,[z478,z28,z2,z4,z5,z6]),(0,[z0,z1107,z2,z4,z5,z6]),(0,[z0,z1,z142,z4,z5,z21]),(0,[z0,z1108,z1,z4,z5,z6]),(0,[z0,z1,z18,z485,z5,z6]),(0,[z0,z1,z1109,z4,z5,z6]),(0,[z0,z1110,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z755])],[(0,[z0,z28,z804,z4,z5,z6]),(0,[z0,z1,z2,z4,z1111,z6]),(0,[z529,z11,z2,z4,z5,z6]),(0,[z114,z1,z287,z4,z5,z130]),(0,[z1112,z0,z2,z4,z5,z6]),(0,[z0,z1,z284,z4,z37,z38])],[(0,[z0,z1113,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1114]),(0,[z0,z2,z4,z117,z615,z6]),(0,[z96,z0,z2,z4,z5,z623]),(0,[z0,z1,z2,z4,z5,z214])],[(0,[z0,z245,z116,z4,z5,z6]),(0,[z0,z11,z119,z4,z5,z6]),(0,[z0,z1,z4,z5,z1115,z6]),(0,[z1116,z1,z2,z4,z5,z6]),(0,[z0,z1,z1117,z2,z4,z5]),(0,[z0,z1,z4,z5,z129,z459])],[(0,[z121,z28,z2,z4,z5,z6]),(0,[z0,z11,z374,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1118]),(0,[z0,z1,z2,z4,z5,z1119]),(0,[z162,z0,z1,z4,z233,z56])]],
   [[(0,[z0,z1,z2,z4,z5,z1120]),(0,[z0,z1121,z2,z4,z5,z6]),(0,[z604,z1,z2,z4,z5,z74]),(0,[z0,z257,z1,z4,z5,z130]),(0,[z0,z1,z4,z172,z984,z6])],[(0,[z27,z759,z2,z4,z5,z6]),(0,[z20,z11,z2,z135,z5,z6]),(0,[z211,z1,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z1122,z6]),(0,[z0,z1,z2,z727,z5,z6]),(0,[z0,z1,z2,z4,z1123,z6]),(0,[z0,z1,z374,z44,z5,z148])],[(0,[z0,z1,z2,z4,z1124,z6]),(0,[z224,z1,z2,z135,z5,z6]),(0,[z0,z528,z1,z4,z5,z148]),(0,[z0,z1,z4,z5,z1125,z6]),(0,[z367,z1,z24,z4,z5,z6]),(0,[z0,z1126,z2,z4,z5,z6])],[(0,[z0,z1,z1127,z4,z5,z6]),(0,[z0,z11,z1030,z4,z5,z6]),(0,[z0,z22,z371,z4,z5,z6]),(0,[z220,z0,z2,z4,z36,z6])],[(0,[z73,z28,z2,z4,z61,z6]),(0,[z28,z2,z4,z5,z6,z166]),(0,[z0,z11,z2,z4,z92,z6]),(0,[z0,z22,z2,z4,z5,z409]),(0,[z663,z0,z1,z55,z5,z6]),(0,[z0,z1128,z2,z4,z5,z6])],[(0,[z0,z1129,z2,z4,z5,z6]),(0,[z0,z1,z119,z4,z5,z21]),(0,[z0,z1,z2,z135,z92,z6]),(0,[z0,z1,z2,z1130,z5,z6]),(0,[z0,z1,z128,z4,z5,z745])],[(0,[z0,z28,z85,z4,z5,z6]),(0,[z23,z0,z28,z2,z41,z6]),(0,[z0,z1,z831,z4,z5,z6]),(0,[z0,z2,z4,z5,z837,z6]),(0,[z0,z1,z128,z4,z5,z674])],[(0,[z0,z1,z2,z4,z5,z1131]),(0,[z0,z1132,z2,z4,z5,z6]),(0,[z0,z424,z2,z4,z5,z293]),(0,[z13,z1,z2,z4,z62,z409]),(0,[z123,z192,z2,z4,z5,z74]),(1,[z0,z758,z4,z5,z6])]],
   [[(0,[z11,z542,z2,z4,z5,z6]),(0,[z211,z1,z997,z4,z5,z6]),(0,[z20,z1,z2,z135,z5,z21]),(0,[z0,z1,z371,z4,z5,z14]),(0,[z1133,z1,z2,z4,z5,z6]),(0,[z0,z324,z2,z4,z5,z6]),(0,[z0,z1,z2,z714,z5,z6]),(0,[z0,z324,z24,z4,z5,z6])],[(0,[z27,z28,z2,z29,z5,z6]),(0,[z0,z245,z375,z4,z5,z6]),(0,[z0,z1,z2,z4,z1134,z5])],[(0,[z429,z11,z2,z4,z5,z6]),(0,[z0,z1135,z1,z2,z4,z5]),(0,[z0,z69,z2,z4,z53,z6])],[(0,[z0,z1,z2,z1136,z5,z6]),(0,[z64,z500,z2,z303,z5,z6]),(0,[z0,z1,z24,z4,z5,z265]),(0,[z0,z1,z2,z4,z5,z265])],[(0,[z367,z69,z2,z4,z5,z6])],[(0,[z9,z1,z2,z135,z5,z6]),(0,[z0,z1137,z2,z4,z5,z6]),(0,[z1,z997,z147,z4,z5,z6]),(0,[z0,z2,z4,z5,z1138,z6]),(0,[z0,z1,z2,z34,z5,z409]),(0,[z0,z1,z2,z4,z1139,z6]),(0,[z0,z1,z4,z1140,z5,z6])],[(0,[z0,z1015,z28,z2,z4,z5]),(0,[z1141,z0,z28,z2,z4,z6]),(0,[z0,z28,z131,z2,z4,z5]),(0,[z0,z1080,z1,z2,z4,z5]),(0,[z500,z463,z2,z4,z5,z6]),(0,[z0,z1,z1142,z4,z5,z6]),(0,[z0,z1143,z2,z4,z5,z6]),(0,[z0,z1144,z2,z4,z5,z6])],[(0,[z0,z11,z2,z4,z37,z38]),(0,[z0,z1,z2,z4,z5,z850]),(0,[z0,z1,z2,z4,z5,z1145]),(0,[z0,z1,z2,z4,z5,z1146]),(0,[z0,z1,z232,z4,z569,z6]),(0,[z0,z1,z18,z578,z5,z6]),(0,[z0,z257,z1,z4,z5,z304])]],
   [[(0,[z0,z28,z2,z4,z138,z6]),(0,[z1141,z0,z1,z2,z4,z6]),(0,[z123,z1,z2,z4,z5,z747]),(0,[z0,z1,z2,z4,z5,z1147]),(0,[z0,z1,z2,z4,z139,z442])],[(1,[z709,z2,z4,z5,z6]),(0,[z0,z28,z142,z4,z5,z6]),(0,[z326,z28,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z353]),(0,[z0,z1148,z2,z4,z5,z6])],[(0,[z0,z11,z4,z5,z913,z6]),(0,[z0,z1,z4,z5,z1149,z6]),(0,[z0,z1,z1150,z4,z5,z6]),(0,[z0,z1151,z2,z4,z5,z6])],[],[(0,[z0,z28,z2,z49,z53,z6]),(0,[z1152,z1,z2,z4,z5,z6]),(0,[z0,z43,z1,z4,z294,z5]),(0,[z0,z257,z1,z4,z5,z204]),(0,[z0,z1,z2,z4,z105,z8])],[(0,[z28,z2,z4,z675,z5,z6]),(0,[z0,z1,z2,z4,z5,z1153]),(0,[z227,z1,z2,z4,z61,z6]),(0,[z0,z69,z2,z4,z5,z265])],[(0,[z0,z1,z2,z4,z5,z926]),(0,[z0,z1,z2,z29,z92,z6]),(0,[z0,z86,z2,z4,z650,z5]),(0,[z0,z1,z2,z4,z5,z1154]),(0,[z0,z1,z4,z5,z129,z304]),(0,[z0,z324,z2,z4,z5,z215])],[(0,[z0,z1,z2,z1155,z5,z6]),(0,[z259,z28,z2,z4,z5,z6]),(0,[z20,z1,z2,z135,z92,z6]),(0,[z27,z99,z2,z29,z5,z6]),(0,[z13,z72,z2,z4,z62,z6]),(0,[z500,z1,z2,z4,z139,z6]),(0,[z0,z1,z102,z4,z5,z442])]],
   [[(0,[z0,z1,z2,z4,z1156,z6]),(0,[z1,z2,z135,z5,z92,z6]),(0,[z0,z1,z2,z4,z438,z5]),(0,[z671,z0,z1,z2,z41,z6]),(0,[z584,z0,z1,z4,z56,z6]),(0,[z0,z1,z2,z53,z730,z6])],[(0,[z7,z28,z2,z4,z5,z6]),(0,[z1,z2,z34,z5,z62,z6]),(0,[z0,z1,z2,z4,z269,z8]),(0,[z0,z1157,z1,z2,z4,z5]),(0,[z0,z1158,z2,z4,z5,z6])],[(0,[z0,z11,z2,z4,z5,z118]),(0,[z582,z1,z2,z29,z5,z6]),(0,[z0,z22,z2,z4,z5,z14]),(0,[z669,z1,z2,z4,z5,z74]),(0,[z0,z2,z4,z303,z137,z6]),(0,[z0,z1,z2,z4,z5,z1159])],[(0,[z0,z1,z1160,z4,z5,z6]),(0,[z267,z28,z25,z4,z5,z6]),(0,[z0,z28,z119,z4,z5,z6]),(0,[z28,z2,z4,z249,z5,z6]),(0,[z0,z1161,z2,z4,z5,z6]),(0,[z0,z72,z2,z195,z5,z6]),(0,[z0,z1,z2,z1162,z5,z6]),(0,[z0,z528,z1,z4,z5,z6]),(0,[z0,z2,z4,z1163,z5,z6]),(0,[z1164,z1,z2,z4,z5,z6])],[(0,[z0,z28,z374,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z442]),(0,[z629,z1,z147,z4,z5,z6]),(0,[z1,z2,z4,z34,z62,z6]),(0,[z0,z341,z85,z4,z5,z6]),(0,[z0,z1,z4,z5,z984,z6])],[(0,[z0,z1165,z2,z4,z5,z6]),(0,[z511,z28,z2,z4,z5,z6]),(0,[z0,z11,z287,z4,z5,z6]),(0,[z0,z11,z257,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1166]),(0,[z0,z424,z2,z4,z5,z21]),(0,[z0,z72,z2,z34,z5,z6]),(0,[z1,z2,z4,z5,z6,z747]),(0,[z0,z1,z2,z4,z1167,z5]),(0,[z1168,z1,z2,z4,z5,z6]),(0,[z1169,z1,z2,z4,z5,z6]),(0,[z64,z0,z150,z303,z5,z6]),(0,[z0,z1,z4,z5,z129,z745]),(1,[z0,z1,z2,z4,z724])],[(0,[z20,z28,z2,z135,z5,z6]),(0,[z0,z1,z371,z4,z5,z6]),(0,[z0,z1,z2,z4,z1170,z5]),(0,[z1171,z1,z2,z4,z5,z6])],[(0,[z79,z0,z28,z2,z5,z52]),(0,[z656,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z409]),(0,[z73,z466,z2,z4,z61,z6]),(0,[z114,z372,z2,z4,z5,z130]),(0,[z0,z1,z4,z5,z351,z118])]],
   [[(0,[z1172,z1,z2,z4,z5,z6])],[(0,[z0,z1173,z2,z4,z5,z6]),(0,[z0,z1,z2,z34,z62,z6]),(1,[z1,z2,z4,z767,z6]),(0,[z0,z1174,z2,z4,z5,z6]),(0,[z79,z0,z1,z2,z5,z52])],[(0,[z9,z0,z2,z379,z5,z6]),(0,[z0,z1,z2,z4,z5,z949]),(0,[z0,z1,z2,z1175,z5,z6]),(0,[z0,z1,z2,z1176,z5,z6]),(0,[z32,z1,z147,z4,z5,z6]),(0,[z0,z1,z1177,z4,z5,z6]),(0,[z0,z218,z1,z4,z55,z5]),(0,[z0,z86,z528,z1,z4,z5]),(0,[z0,z1,z17,z714,z5,z6]),(0,[z1178,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1179,z6]),(0,[z0,z1,z2,z4,z951,z5]),(0,[z0,z11,z4,z294,z5,z6]),(0,[z0,z1,z2,z4,z5,z1180]),(0,[z0,z1,z2,z4,z5,z1181]),(0,[z391,z26,z2,z4,z5,z6]),(0,[z0,z324,z638,z4,z5,z6])],[(0,[z555,z0,z1,z2,z41,z6]),(0,[z1182,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1183]),(0,[z0,z1,z2,z578,z5,z148]),(0,[z156,z324,z2,z4,z5,z6]),(0,[z0,z1,z2,z44,z5,z755])],[(0,[z0,z1,z1100,z2,z4,z5]),(0,[z0,z758,z2,z4,z5,z6]),(0,[z0,z1,z2,z843,z5,z6]),(0,[z0,z1184,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1185,z6])],[(0,[z580,z0,z1,z2,z41,z6]),(0,[z1186,z1,z2,z4,z5,z6]),(0,[z0,z1,z638,z4,z5,z265])],[(0,[z0,z28,z128,z4,z5,z129]),(0,[z0,z1187,z2,z4,z5,z6]),(0,[z0,z1,z232,z4,z984,z6]),(0,[z156,z1,z2,z4,z5,z265])]],
   [[(0,[z167,z0,z2,z4,z36,z6]),(0,[z0,z1,z2,z4,z5,z1188])],[(0,[z0,z1073,z28,z2,z4,z5]),(0,[z123,z11,z2,z4,z5,z74]),(0,[z0,z1,z2,z4,z5,z1189])],[(0,[z0,z1,z2,z1190,z5,z6]),(0,[z1191,z1,z2,z4,z5,z6]),(0,[z162,z0,z1,z4,z56,z298]),(1,[z0,z1,z2,z730,z6])],[(0,[z0,z45,z2,z4,z5,z6]),(0,[z1,z2,z4,z767,z62,z6]),(0,[z0,z1,z2,z4,z5,z1192]),(0,[z0,z1,z2,z4,z137,z125]),(0,[z0,z1,z2,z4,z5,z1193]),(0,[z0,z1,z4,z984,z56,z6]),(0,[z1194,z1,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z233,z5]),(0,[z0,z99,z2,z4,z5,z6]),(0,[z0,z424,z2,z4,z92,z6]),(0,[z513,z0,z2,z4,z36,z6]),(0,[z0,z1,z2,z1195,z5,z6]),(0,[z0,z725,z2,z4,z5,z6]),(0,[z0,z1,z1196,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1197]),(0,[z0,z1198,z2,z4,z5,z6])],[(0,[z109,z28,z2,z135,z5,z6]),(0,[z114,z28,z2,z4,z5,z130]),(0,[z0,z1,z2,z1199,z5,z6]),(0,[z0,z1200,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z837,z87]),(0,[z0,z1201,z2,z4,z5,z6]),(0,[z0,z1202,z2,z4,z5,z6]),(0,[z0,z1203,z2,z4,z5,z6])],[(0,[z0,z11,z4,z5,z966,z6]),(0,[z0,z1204,z2,z4,z5,z6]),(0,[z0,z1205,z2,z4,z5,z6]),(0,[z1206,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1207]),(0,[z0,z2,z4,z5,z736,z6]),(0,[z0,z1,z1208,z4,z5,z6])],[(0,[z11,z332,z2,z4,z5,z6]),(0,[z0,z84,z2,z4,z138,z6]),(0,[z0,z1,z2,z4,z65,z5]),(0,[z0,z1209,z2,z4,z5,z6])]],
   [[(0,[z1210,z0,z2,z4,z5,z6]),(0,[z0,z22,z2,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z1120]),(0,[z0,z1,z2,z4,z5,z1211]),(0,[z0,z84,z142,z4,z5,z6]),(0,[z1212,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z298])],[(0,[z0,z1,z1213,z4,z5,z6]),(0,[z0,z11,z2,z4,z5,z974]),(0,[z73,z1,z2,z4,z61,z6]),(0,[z391,z1,z2,z4,z139,z6]),(0,[z0,z1,z18,z4,z5,z231]),(0,[z0,z1,z1214,z4,z5,z6])],[(0,[z367,z11,z2,z4,z5,z6]),(0,[z0,z1,z18,z579,z5,z6]),(0,[z0,z26,z2,z338,z5,z6])],[(0,[z0,z1,z85,z4,z5,z6]),(0,[z0,z1,z1215,z4,z5,z6]),(0,[z0,z2,z93,z843,z5,z6]),(0,[z77,z0,z1,z714,z5,z6]),(0,[z0,z1,z2,z4,z5,z1216]),(0,[z0,z2,z4,z1217,z5,z6]),(0,[z0,z1218,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1219,z5,z6]),(0,[z0,z341,z2,z4,z5,z6]),(0,[z391,z1,z150,z4,z5,z6])],[(0,[z629,z28,z2,z4,z5,z6]),(0,[z0,z1,z1220,z4,z5,z6]),(0,[z211,z310,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z14]),(0,[z495,z0,z2,z4,z5,z51])],[(0,[z28,z2,z4,z5,z315,z6]),(0,[z0,z28,z4,z5,z927,z6]),(0,[z0,z11,z4,z5,z351,z6]),(0,[z27,z1,z2,z29,z5,z6]),(0,[z0,z1,z1221,z4,z5,z6]),(0,[z1222,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1223])],[(0,[z28,z319,z2,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z118]),(0,[z0,z45,z2,z4,z5,z631]),(0,[z0,z1224,z2,z4,z5,z6])]],
   [[(0,[z0,z28,z232,z4,z172,z6]),(0,[z28,z2,z4,z108,z5,z6]),(0,[z0,z11,z2,z4,z5,z21]),(0,[z224,z0,z1,z2,z41,z6]),(0,[z0,z2,z4,z5,z1225,z6]),(0,[z0,z1,z2,z4,z5,z1226]),(0,[z391,z1,z102,z4,z5,z6]),(0,[z0,z2,z4,z5,z51,z837])],[(0,[z27,z1,z2,z30,z5,z6]),(0,[z0,z1,z1227,z4,z5,z6]),(0,[z0,z1,z2,z34,z5,z6]),(0,[z0,z1228,z2,z4,z5,z6]),(0,[z222,z1,z2,z4,z5,z74])],[(0,[z0,z1229,z2,z4,z5,z6]),(0,[z156,z28,z2,z4,z5,z6]),(0,[z0,z1230,z2,z4,z5,z6]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z125]),(0,[z220,z0,z2,z4,z117,z6]),(0,[z0,z43,z1,z4,z689,z5]),(0,[z0,z257,z1,z4,z37,z38])],[(0,[z0,z1231,z2,z4,z5,z6]),(0,[z0,z1232,z2,z4,z5,z6]),(0,[z0,z26,z2,z843,z5,z6]),(0,[z0,z1233,z2,z4,z5,z6]),(0,[z1234,z1,z2,z4,z5,z6])],[(0,[z0,z947,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z137,z6]),(0,[z0,z1,z301,z4,z438,z5]),(0,[z0,z1,z4,z233,z294,z5]),(0,[z0,z1235,z2,z4,z5,z6])],[(0,[z0,z28,z4,z938,z5,z6]),(0,[z0,z84,z2,z4,z5,z6]),(0,[z391,z11,z2,z4,z5,z6]),(0,[z0,z86,z2,z4,z5,z518]),(0,[z0,z1,z2,z4,z138,z6]),(0,[z0,z1236,z2,z4,z5,z6]),(0,[z0,z86,z2,z4,z5,z87]),(0,[z162,z0,z1,z4,z984,z6])],[(0,[z0,z1113,z28,z4,z5,z6]),(0,[z0,z1,z142,z4,z5,z6]),(0,[z0,z1,z1237,z4,z5,z6]),(0,[z0,z1,z4,z1238,z5,z6]),(0,[z391,z90,z2,z4,z5,z6])],[(0,[z0,z28,z2,z4,z5,z293]),(0,[z0,z1,z808,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1239]),(0,[z1,z2,z4,z727,z5,z6]),(0,[z73,z1,z2,z4,z313,z6]),(0,[z96,z0,z257,z1,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 519) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1047).take 213) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1260)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 519, 213] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 102).take 96).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 198).take 58).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [102, 96, 58] = true :=
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

end PEqualNP.Outside.L_meta_37721

theorem PEqualNP.Outside.L_meta_37721 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37721.solve