import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45782

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
  Nat.testBit (4008241896 * 2 ^ 32 + 4008232960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x202289c364386f0c#64 ++ 0x0808a270d90e1bc3#64 ++ 0xe4679fc7ec78ff1e#64 ++ 0xf919e7f1fb1e3fc7#64 : BitVec 256),
   (0x41892458a18b1574#64 ++ 0x106249162862c55d#64 ++ 0xfb99e478f38f1fff#64 ++ 0xfee6791e3ce3c7ff#64 : BitVec 256),
   (0x8c14586d1c0da3a0#64 ++ 0x2305161b470368e8#64 ++ 0xcc1e787f1c0fe3e3#64 ++ 0x73079e1fc703f8f8#64 : BitVec 256),
   (0x0ec07e801ed002d8#64 ++ 0x83b01fa007b400b6#64 ++ 0xffe07f801ff003ff#64 ++ 0xbff81fe007fc00ff#64 : BitVec 256),
   (0x1f7f80001b66d800#64 ++ 0x47dfe00006d9b600#64 ++ 0x7fff80001ffffc03#64 ++ 0xdfffe00007ffff00#64 : BitVec 256),
   (0x1ffff736c0000001#64 ++ 0x07fffdcdb0000000#64 ++ 0x9fffffffe0000003#64 ++ 0xe7fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z1 : W := mkw 0x113f8136c0000001 0x044fe04db0000000 0x001f807fe0000000 0x4007e01ff8000000

def z2 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z3 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z4 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z5 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z6 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z7 : W := mkw 0x0e40520000000000 0x0390148000000000 0x04601b8000000000 0x011806e000000000

def z8 : W := mkw 0x0ec0760000000000 0x03b01d8000000000 0x9fe07f8000000003 0xa7f81fe000000000

def z9 : W := mkw 0x1fffffb6ded002d9 0x87ffffedb7b400b6 0xfffffffffff003ff 0xfffffffffffc00ff

def z10 : W := mkw 0x0000000018048000 0x0000000006012000 0x400000001c0fe000 0x100000000703f800

def z11 : W := mkw 0x0022800000204800 0x0008a00000081200 0x646780000c78fc02 0xd919e000031e3f00

def z12 : W := mkw 0x40802458a0890574 0x102009162822415d 0x80006478e00003fc 0x2000191e380000ff

def z13 : W := mkw 0x2022898364306e0c 0x0808a260d90c1b83 0x24679f87ec70fc1c 0x8919e7e1fb1c3f07

def z14 : W := mkw 0x9f7fd8251f66fa80 0x67dff60947d9bea0 0x7fff98071ffffc03 0xdfffe601c7ffff00

def z15 : W := mkw 0xac36d9e77c3cef8c 0x2b0db679df0f3be3 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z16 : W := mkw 0x1ffff736db66d801 0x47fffdcdb6d9b600 0xfffffffffffffc03 0xffffffffffffff00

def z17 : W := mkw 0x1ffffe801ff6dad8 0xc7ffffa007fdb6b6 0xffffff801fffffff 0xffffffe007ffffff

def z18 : W := mkw 0x40000048218b1574 0x100000120862c55d 0x60000000138f1ffc 0x1800000004e3c7ff

def z19 : W := mkw 0x3fffffb7c4306a09 0x0fffffedf10c1a82 0x9fffffffec70e003 0xe7fffffffb1c3800

def z20 : W := mkw 0x113f80000126d800 0x444fe0000049b600 0x001f8000000ffc00 0x4007e0000003ff00

def z21 : W := mkw 0x02c0268002d00058 0x80b009a000b40016 0x33e0078003f0001c 0x8cf801e000fc0007

def z22 : W := mkw 0x0c0058001c000280 0x03001600070000a0 0xcc0078001c0003e3 0x33001e00070000f8

def z23 : W := mkw 0x2022898344306a08 0x0808a260d10c1a82 0x04661b870c70e000 0x011986e1c31c3800

def z24 : W := mkw 0x612b815be12b7d24 0x184ae056f84adf49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z25 : W := mkw 0x0080268000900058 0x802009a000240016 0x000007800000001c 0x000001e000000007

def z26 : W := mkw 0xcfdd7efdbfdfb7fc 0xb3f75fbf6ff7edff 0xffffffffffffffff 0xffffffffffffffff

def z27 : W := mkw 0x1e7680001a64c800 0x479da00006993200 0x4c7e00001c7fe003 0x531f8000071ff800

def z28 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x80079fc7e008ff1c 0x6001e7f1f8023fc7

def z29 : W := mkw 0x0080240000800050 0x0020090000200014 0xfb806400138003ff 0xbee0190004e000ff

def z30 : W := mkw 0x4fc97ed8bfdb17fc 0x93f25fb62ff6c5ff 0xfff9fff8ffff1fff 0xfffe7ffe3fffc7ff

def z31 : W := mkw 0x41090058a10b1524 0x104240162842c549 0x00198078e00f1c00 0x4006601e3803c700

def z32 : W := mkw 0x8ed47eed1edda3f8 0xa3b51fbb47b768fe 0xfffe7fff1fffe3ff 0xffff9fffc7fff8ff

def z33 : W := mkw 0x41aba458a1ab5d74 0x106ae916286ad75d 0xffffe478ffffffff 0xfffff91e3fffffff

def z34 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x1bf9e7b8e0000001 0x86fe79ee38000000

def z35 : W := mkw 0x5ffff736e1821455 0x17fffdcdb8608515 0xbfffffffe3801c1f 0xeffffffff8e00707

def z36 : W := mkw 0x13eba712c0000001 0x04fae9c4b0000000 0x9bf9e7f8e0000003 0xe6fe79fe38000000

def z37 : W := mkw 0x1e76da801e74ca88 0xc79db6a0079d32a2 0x04661b800c70e000 0x011986e0031c3800

def z38 : W := mkw 0x1e76d32640000001 0x079db4c990000000 0x04661b8700000000 0x011986e1c0000000

def z39 : W := mkw 0x0fc97e909ed002d8 0x83f25fa427b400b6 0xfff9fff8fff003ff 0xfffe7ffe3ffc00ff

def z40 : W := mkw 0x0c14502400000000 0x0305140900000000 0x8c1e787f00000003 0x63079e1fc0000000

def z41 : W := mkw 0x9fffff7fdc0da3a1 0x27ffffdff70368e8 0xdffffffffc0fe3e3 0xf7ffffffff03f8f8

def z42 : W := mkw 0xa00008c93c3defac 0x280002324f0f7beb 0x600000001c7ffffc 0x18000000071fffff

def z43 : W := mkw 0xac36d9ef7c3defac 0x2b0db67bdf0f7beb 0xec7ffffffc7fffff 0xfb1fffffff1fffff

def z44 : W := mkw 0xac1459ef7c1da7ac 0x2b05167bdf0769eb 0xcc1e7ffffc0fe3ff 0x73079fffff03f8ff

def z45 : W := mkw 0x0022810240000000 0x0008a04090000000 0x84679fc7e0000002 0xe119e7f1f8000000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z47 : W := mkw 0x9fffff7fdf6ffba1 0x67ffffdff7dbfee8 0xffffffffffffffe3 0xfffffffffffffff8

def z48 : W := mkw 0x1e76d3265a64c801 0x479db4c996993200 0x04661b870c70e000 0x011986e1c31c3800

def z49 : W := mkw 0x00807736c0000001 0x00201dcdb0000000 0x80007fffe0000000 0x20001ffff8000000

def z50 : W := mkw 0x0ec07fb6ded002d9 0x83b01fedb7b400b6 0xffe07ffffff003ff 0xbff81ffffffc00ff

def z51 : W := mkw 0x913f817fc00da121 0x244fe05ff0036848 0x001f807fe00fe000 0x4007e01ff803f800

def z52 : W := mkw 0x0014000000048000 0x0005000000012000 0x001e0000000fe000 0x400780000003f800

def z53 : W := mkw 0x1f7fd8001f66da80 0x47dff60007d9b6a0 0xfffff8001fffffe3 0xfffffe0007fffff8

def z54 : W := mkw 0x800008491f6ffba0 0x6000021247dbfee8 0x600000001fffffe0 0x1800000007fffff8

def z55 : W := mkw 0x0ec026801ad00058 0x83b009a006b40016 0x7fe007801ff0001f 0x9ff801e007fc0007

def z56 : W := mkw 0x1f7f81025b66d800 0x47dfe04096d9b600 0xffff9fc7fffffc03 0xffffe7f1ffffff00

def z57 : W := mkw 0x136b800003625800 0x44dae00000d89600 0x7bf9800013ff1c03 0xdefe600004ffc700

def z58 : W := mkw 0x0e4000001a400000 0x0390000006900000 0x7fe000001ff00003 0x9ff8000007fc0000

def z59 : W := mkw 0x8c00586d1c0923a0 0x2300161b470248e8 0xcc00787f1c0003e3 0x33001e1fc70000f8

def z60 : W := mkw 0x00807fb6c49002d9 0x80201fedb12400b6 0x80007fffe00003fc 0x20001ffff80000ff

def z61 : W := mkw 0x13eba712c0000001 0x04fae9c4b0000000 0x13e18780e0000000 0x84f861e038000000

def z62 : W := mkw 0x200009c36418270c 0x08000270d90609c3 0x80001fc7e000031c 0x200007f1f80000c7

def z63 : W := mkw 0x3f7f89c37f7eff0c 0x4fdfe270dfdfbfc3 0xffff9fc7ffffff1f 0xffffe7f1ffffffc7

def z64 : W := mkw 0x5ffff77ee0890575 0x17fffddfb822415d 0x9fffffffe00003ff 0xe7fffffff80000ff

def z65 : W := mkw 0x000000001b66d800 0x4000000006d9b600 0x600000001ffffc00 0x1800000007ffff00

def z66 : W := mkw 0x00807e80049002d8 0x80201fa0012400b6 0x80007f80000003fc 0x20001fe0000000ff

def z67 : W := mkw 0x1f7f8136db66d801 0x47dfe04db6d9b600 0x7fff807ffffffc03 0xdfffe01fffffff00

def z68 : W := mkw 0x8014006d000da120 0x2005001b40036848 0x001e007f000fe000 0x4007801fc003f800

def z69 : W := mkw 0x0022804020284d04 0x0008a010080a1341 0xe4678440ec78ff1e 0xf919e1103b1e3fc7

def z70 : W := mkw 0x000008801e500288 0x80000220079400a2 0x000000000c700000 0x00000000031c0000

def z71 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x04679bc7ec78fc00 0x4119e6f1fb1e3f00

def z72 : W := mkw 0x1f6b80001b625800 0x47dae00006d89600 0x7fe180001ff01c03 0x9ff8600007fc0700

def z73 : W := mkw 0x41090048218b1574 0x104240120862c55d 0x7b998000138f1fff 0xdee6600004e3c7ff

def z74 : W := mkw 0x1f5d00001b469000 0x47d7400006d1a400 0x1b98000013870001 0x06e6000004e1c000

def z75 : W := mkw 0x9f7fd86d1f6ffba0 0x67dff61b47dbfee8 0xfffff87f1fffffe3 0xfffffe1fc7fffff8

def z76 : W := mkw 0x0c14586504082300 0x03051619410208c0 0xcc1e787f0c08e303 0x73079e1fc30238c0

def z77 : W := mkw 0x8ed47ea51ed4a2d8 0xa3b51fa947b528b6 0xffe67f871ff0e3ff 0xbff99fe1c7fc38ff

def z78 : W := mkw 0x8e54586d1e4da3a0 0x2395161b479368e8 0xfffe787f1fffe3e3 0xffff9e1fc7fff8f8

def z79 : W := mkw 0x0000088004100208 0x0000022001040082 0xe4601f800c70031e 0xb91807e0031c00c7

def z80 : W := mkw 0x2022814360286d04 0x0808a050d80a1b41 0x00078047e008fc00 0x4001e011f8023f00

def z81 : W := mkw 0x113f80000126d800 0x444fe0000049b600 0x7b9f8000138ffc03 0xdee7e00004e3ff00

def z82 : W := mkw 0x0e5400001a448000 0x0395000006912000 0x7ffe00001fffe003 0xdfff800007fff800

def z83 : W := mkw 0x0022800000204800 0x0008a00000081200 0x2061800000701c00 0x88186000001c0700

def z84 : W := mkw 0x4fc97e989fd312f8 0x93f25fa627f4c4be 0xfff87fb81ff703ff 0xbffe1fee07fdc0ff

def z85 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x1ffe7bbf00000001 0x07ff9eefc0000000

def z86 : W := mkw 0x8c947f7fdc0da3a1 0x23251fdff70368e8 0xcc1e7ffffc0fe3e3 0x73079fffff03f8f8

def z87 : W := mkw 0x1f7f800000000000 0x07dfe00000000000 0x1fff800000000003 0xc7ffe00000000000

def z88 : W := mkw 0x800008491c0da3a0 0x20000212470368e8 0x400000001c0fe3e0 0x100000000703f8f8

def z89 : W := mkw 0x2022818260304c0c 0x0808a060980c1303 0x20618780e0701c1c 0x881861e0381c0707

def z90 : W := mkw 0x4189777ee18b1575 0x10625ddfb862c55d 0xfb99fffff38f1fff 0xfee67ffffce3c7ff

def z91 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x9b986478f38703fd 0x26e6191e3ce1c0ff

def z92 : W := mkw 0x202289cb64396f2c 0x0808a272d90e5bcb 0xec7ffffffc7fffff 0xfb1fffffff1fffff

def z93 : W := mkw 0x41892410a1821454 0x1062490428608515 0xfb81e400f3801fff 0xbee079003ce007ff

def z94 : W := mkw 0x0000004800090120 0x0000001200024048 0xc8186078100f03e3 0x7206181e0403c0f8

def z95 : W := mkw 0x2022818260304c0c 0x0808a060980c1303 0x64678780ec78fc1e 0xd919e1e03b1e3f07

def z96 : W := mkw 0x1fdd763480000001 0x07f75d8d20000000 0x1b98603800000001 0x06e6180e00000000

def z97 : W := mkw 0x200008c124386f0c 0x08000230490e1bc3 0x600000000c78ff1c 0x18000000031e3fc7

def z98 : W := mkw 0x8c14502418048080 0x2305140906012020 0x0000000000000000 0x0000000000000000

def z99 : W := mkw 0x4189241881831070 0x106249062060c41c 0x1b986038138700e1 0x06e6180e04e1c038

def z100 : W := mkw 0x02c0268002d00058 0x80b009a000b40016 0xfbe0678013f003ff 0xbef819e004fc00ff

def z101 : W := mkw 0x2022898264304e0c 0x0808a260990c1383 0xe4619f80ec701f1e 0xb91867e03b1c07c7

def z102 : W := mkw 0x61892ddbe59b377c 0x18624b76f966cddf 0xfb99fffff38f1fff 0xfee67ffffce3c7ff

def z103 : W := mkw 0x0000084904092320 0x00000212410248c8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z104 : W := mkw 0x61abaddbe5bb7f7c 0x186aeb76f96edfdf 0xffffffffffffffff 0xffffffffffffffff

def z105 : W := mkw 0x0c0058411c082380 0x03001610470208e0 0xcc0678471c08e3e3 0x73019e11c70238f8

def z106 : W := mkw 0x612b89dbe53b7f2c 0x184ae276f94edfcb 0xe47f9fffec7fff1e 0xf91fe7fffb1fffc7

def z107 : W := mkw 0x1ffff63480000001 0x07fffd8d20000000 0x1fffe03800000003 0xc7fff80e00000000

def z108 : W := mkw 0x200009c36418270c 0x08000270d90609c3 0xc4061fc7ec08e31e 0x710187f1fb0238c7

def z109 : W := mkw 0x0189241080000000 0x0062490420000000 0x9b99e478e0000003 0xe6e6791e38000000

def z110 : W := mkw 0x0ec076001ac000d0 0x83b01d8006b00034 0x1b806000138000e1 0x06e0180004e00038

def z111 : W := mkw 0x1ffff736dac000d1 0x87fffdcdb6b00034 0x9ffffffff38000e3 0xe7fffffffce00038

def z112 : W := mkw 0x13ffa736c0000001 0x04ffe9cdb0000000 0x13ff87ffe0000000 0xc4ffe1fff8000000

def z113 : W := mkw 0x0022800000204800 0x0008a00000081200 0x046600000c70e000 0x01198000031c3800

def z114 : W := mkw 0x00807e80049002d8 0x80201fa0012400b6 0xe4607f800c7003fe 0xb9181fe0031c00ff

def z115 : W := mkw 0x0c14000018048000 0x0305000006012000 0x4c1e00001c0fe003 0x530780000703f800

def z116 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x1fe07b801ff000e1 0x07f81ee007fc0038

def z117 : W := mkw 0x0022888004304a08 0x0008a220010c1282 0xe4679f800c78ff1e 0xf919e7e0031e3fc7

def z118 : W := mkw 0x40000058a0090524 0x1000001628024149 0x00000078e0000000 0x0000001e38000000

def z119 : W := mkw 0x00802712c0000001 0x002009c4b0000000 0x00000780e0000000 0x000001e038000000

def z120 : W := mkw 0x000008c02418070c 0x00000230090601c3 0xe4619fc0ec781f1e 0xf91867f03b1e07c7

def z121 : W := mkw 0x0e405a801e500288 0x839016a0079400a2 0x04601b800c700000 0x011806e0031c0000

def z122 : W := mkw 0x8e545aed1e5da3a8 0xa39516bb479768ea 0xcc7e7bff1c7fe3e3 0x731f9effc71ff8f8

def z123 : W := mkw 0x202281c360386d0c 0x0808a070d80e1b43 0x206787c7e078fc1c 0xc819e1f1f81e3f07

def z124 : W := mkw 0x5ffff77ee18b1575 0x17fffddfb862c55d 0xfffffffff38f1fff 0xfffffffffce3c7ff

def z125 : W := mkw 0x1fffffb6de500289 0x87ffffedb79400a2 0x9fffffffec700003 0xe7fffffffb1c0000

def z126 : W := mkw 0x0e405a801e500288 0x839016a0079400a2 0xe4601f800c70031e 0xb91807e0031c00c7

def z127 : W := mkw 0x5fffa4189be7d870 0x57ffe90626f9f61c 0x7fffe0381ffffce3 0xdffff80e07ffff38

def z128 : W := mkw 0x40807ed8a49907fc 0x90201fb6292641ff 0x80007ff8e00003fc 0x20001ffe380000ff

def z129 : W := mkw 0x3f7f89c364386f0c 0x0fdfe270d90e1bc3 0xffff9fc7ec78ff1f 0xffffe7f1fb1e3fc7

def z130 : W := mkw 0x0ee2ff825ed002d8 0x83b8bfe097b400b6 0xffe7ffc7fff003ff 0xfff9fff1fffc00ff

def z131 : W := mkw 0x3f7f81827b76dc0c 0x4fdfe0609eddb703 0x7fff8780fffffc1f 0xdfffe1e03fffff07

def z132 : W := mkw 0x1ffff6001be6d8d0 0xc7fffd8006f9b634 0x7fffe0001ffffce3 0xdffff80007ffff38

def z133 : W := mkw 0x0ed47e801ed482d8 0x83b51fa007b520b6 0xfffe7f801fffe3ff 0xffff9fe007fff8ff

def z134 : W := mkw 0x8c14502c180580a0 0x2305140b06016028 0x8c1e787f100700e3 0x63079e1fc401c038

def z135 : W := mkw 0x1f7f800003625800 0x47dfe00000d89600 0x3fff800003f01c03 0xcfffe00000fc0700

def z136 : W := mkw 0x41892410a1821454 0x1062490428608515 0x33818400e3801c1c 0x8ce0610038e00707

def z137 : W := mkw 0x8c14582d1c05a2a0 0x2305160b470168a8 0x0c1e783f1c07e0e1 0x03079e0fc701f838

def z138 : W := mkw 0x41892450a18a1554 0x1062491428628555 0xf3818440e3881f1e 0xfce0611038e207c7

def z139 : W := mkw 0x1f7fda801f76da88 0xc7dff6a007ddb6a2 0x7fff9b801ffffc03 0xdfffe6e007ffff00

def z140 : W := mkw 0x0000088004100208 0x0000022001040082 0x04601b800c700000 0x011806e0031c0000

def z141 : W := mkw 0x0c140048180d8120 0x0305001206036048 0xcc1e60781c0fe3e3 0x7307981e0703f8f8

def z142 : W := mkw 0x200009c36418270c 0x08000270d90609c3 0xe0019fc7e0081f1e 0xf80067f1f80207c7

def z143 : W := mkw 0x0ec0768002d00058 0x83b01da000b40016 0xbfe07f8003f0001f 0xaff81fe000fc0007

def z144 : W := mkw 0x0000000000000000 0x0000000000000000 0x84601f8000000002 0xa11807e000000000

def z145 : W := mkw 0x02c0260002c00050 0x80b0098000b00014 0x1380000003800000 0x04e0000000e00000

def z146 : W := mkw 0x1fffa712c0000001 0x07ffe9c4b0000000 0x1fff8780e0000003 0xc7ffe1e038000000

def z147 : W := mkw 0x41897ed8a59b17fc 0x90625fb62966c5ff 0xfb99fff8f38f1fff 0xfee67ffe3ce3c7ff

def z148 : W := mkw 0x40000048210b1524 0x100000120842c549 0x00000000000f1c00 0x000000000003c700

def z149 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x7b8060001ff003fd 0x1ee0180007fc00ff

def z150 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x1ffe00001ff7e001 0x07ff800007fdf800

def z151 : W := mkw 0x8c14586d3c0da7a4 0x2305161b4f0369e9 0xec1ffc7ffc0fffff 0xfb07ff1fff03ffff

def z152 : W := mkw 0x0c0058801c100288 0x03001620070400a2 0xec607f801c7003ff 0xbb181fe0071c00ff

def z153 : W := mkw 0x0080760000000000 0x00201d8000000000 0x80007f8000000000 0x20001fe000000000

def z154 : W := mkw 0xac36d96f7c2defa4 0x2b0db65bdf0b7be9 0xcc1ff87ffc0fffe3 0x7307fe1fff03fff8

def z155 : W := mkw 0x0109000001021000 0x0042400000408400 0x7b998000138f1c03 0xdee6600004e3c700

def z156 : W := mkw 0x41892458bbefdd74 0x506249162efbf75d 0xfb99e478ffffffff 0xfee6791e3fffffff

def z157 : W := mkw 0x1f7f80481b6fd920 0x47dfe01206dbf648 0xffffe0781fffffe3 0xfffff81e07fffff8

def z158 : W := mkw 0x1ffff736c126d801 0x47fffdcdb049b600 0x9fffffffe00ffc03 0xe7fffffff803ff00

def z159 : W := mkw 0x000008001c000280 0x00000200070000a0 0x400000001c0003e0 0x10000000070000f8

def z160 : W := mkw 0x2c22d9c37c386f8c 0x0b08b670df0e1be3 0xec67ffc7fc78ffff 0xfb19fff1ff1e3fff

def z161 : W := mkw 0x9e76d86d1e6deba0 0x679db61b479b7ae8 0xcc7e787f1c7fe3e3 0x731f9e1fc71ff8f8

def z162 : W := mkw 0x1ef6ffa65ed002d9 0x87bdbfe997b400b6 0xffe67f871ff003ff 0xbff99fe1c7fc00ff

def z163 : W := mkw 0x3e76dbe764386f0d 0x0f9db6f9d90e1bc3 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z164 : W := mkw 0x9e76db275c04a281 0x279db6c9d70128a0 0x04661b870c00e000 0x011986e1c3003800

def z165 : W := mkw 0x012b800001225800 0x004ae00000489600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z166 : W := mkw 0x1e7680001a64c800 0x479da00006993200 0x7fe600001ff0e003 0x9ff9800007fc3800

def z167 : W := mkw 0x4d897c58bd8b17f4 0x13625f162f62c5fd 0xff99fc78ff8f1fff 0xffe67f1e3fe3c7ff

def z168 : W := mkw 0x1f5d00001b469000 0x47d7400006d1a400 0x5f9e00001f8fe003 0x57e7800007e3f800

def z169 : W := mkw 0x41892458818b1170 0x106249162062c45c 0xdb986078138f03e3 0x76e6181e04e3c0f8

def z170 : W := mkw 0x313f89c3653eff0c 0x4c4fe270d94fbfc3 0xe47f9fc7ec7fff1e 0xf91fe7f1fb1fffc7

def z171 : W := mkw 0x1ffff736c0800051 0x07fffdcdb0200014 0xfffffffff38003ff 0xfffffffffce000ff

def z172 : W := mkw 0x8d1d586d1d0fb3a0 0x2347561b4743ece8 0xff9ff87f1f8fffe3 0xffe7fe1fc7e3fff8

def z173 : W := mkw 0x313f89f7e4386f0d 0x0c4fe27df90e1bc3 0xe47f9fffec78ff1e 0xf91fe7fffb1e3fc7

def z174 : W := mkw 0x4080241880810070 0x102009062020401c 0x00006038000000e0 0x0000180e00000038

def z175 : W := mkw 0x5fffa458a18b1574 0x17ffe9162862c55d 0xffffe478f38f1fff 0xfffff91e3ce3c7ff

def z176 : W := mkw 0x0ec076001a400000 0x03b01d8006900000 0xffe07f801ff00003 0xbff81fe007fc0000

def z177 : W := mkw 0x1fdd7736c0000001 0x07f75dcdb0000000 0x9b987fffe0000001 0x26e61ffff8000000

def z178 : W := mkw 0x1fffa41080000000 0x07ffe90420000000 0x9fffe478e0000003 0xe7fff91e38000000

def z179 : W := mkw 0x202281c260384d0c 0x0808a070980e1343 0xe06187c0e0781f1e 0xf81861f0381e07c7

def z180 : W := mkw 0x0022884104286b00 0x0008a210410a1ac0 0xe46798470c78ff02 0xf919e611c31e3fc0

def z181 : W := mkw 0x1e7680001b66d800 0x479da00006d9b600 0x646600001ffffc00 0x1919800007ffff00

def z182 : W := mkw 0x8c1458251c04a280 0x23051609470128a0 0x040618070c00e000 0x01018601c3003800

def z183 : W := mkw 0x0ec07ec81ed903f8 0x83b01fb207b640fe 0xfff87ff81fff03ff 0xfffe1ffe07ffc0ff

def z184 : W := mkw 0x8c1458ed1c1da3a8 0x2305163b470768ea 0xec7e7fff1c7fe3ff 0xfb1f9fffc71ff8ff

def z185 : W := mkw 0x9ffff73ed80580a1 0x27fffdcfb6016028 0x9ffffffff00700e3 0xe7fffffffc01c038

def z186 : W := mkw 0x8c14506d180da1a0 0x2305141b46036868 0x081e607f100fe0e1 0x4207981fc403f838

def z187 : W := mkw 0x0080240000800050 0x0020090000200014 0x1b806000138000e1 0x06e0180004e00038

def z188 : W := mkw 0x202289c37f7eff0c 0x4808a270dfdfbfc3 0xe4679fc7ffffff1e 0xf919e7f1ffffffc7

def z189 : W := mkw 0xac36d9ef5c3deba8 0x2b0db67bd70f7aea 0xcc7e7bff1c7fe3e3 0x731f9effc71ff8f8

def z190 : W := mkw 0x41892458a10b1524 0x106249162842c549 0x9b99e478e00f1c03 0xe6e6791e3803c700

def z191 : W := mkw 0x1f7fd0241b66d800 0x47dff40906d9b600 0xfffff87f1ffffc03 0xfffffe1fc7ffff00

def z192 : W := mkw 0x40802458a0890574 0x102009162822415d 0xfb806478f38003ff 0xbee0191e3ce000ff

def z193 : W := mkw 0x000008801ed002d8 0x8000022007b400b6 0x600000001ff003fc 0x1800000007fc00ff

def z194 : W := mkw 0x8c14502c180580a0 0x2305140b06016028 0x08186038100700e1 0x0206180e0401c038

def z195 : W := mkw 0xcd9d7c7dbd8fb7f4 0x33675f1f6f63edfd 0xff9ffc7fff8fffff 0xffe7ff1fffe3ffff

def z196 : W := mkw 0x0e6280001a604800 0x0398a00006981200 0x7fe780001ff8fc03 0xdff9e00007fe3f00

def z197 : W := mkw 0x0189241081021000 0x0062490420408400 0xfb99e478f38f1c03 0xfee6791e3ce3c700

def z198 : W := mkw 0x0000532640000001 0x000014c990000000 0x00001b8700000000 0x000006e1c0000000

def z199 : W := mkw 0x0e4000001a400000 0x0390000006900000 0x1b80000013800001 0x06e0000004e00000

def z200 : W := mkw 0x1f7f80000126d800 0x47dfe0000049b600 0x1fff8000000ffc03 0xc7ffe0000003ff00

def z201 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00004000000031e 0xb8000100000000c7

def z202 : W := mkw 0x8c14586d040923a0 0x2305161b410248e8 0x8c1e787f000003e3 0x63079e1fc00000f8

def z203 : W := mkw 0x200008c124386f0c 0x08000230490e1bc3 0xe0018440ec78ff1e 0xf80061103b1e3fc7

def z204 : W := mkw 0x9fffff7fc40923a1 0x27ffffdff10248e8 0x9fffffffe00003e3 0xe7fffffff80000f8

def z205 : W := mkw 0xbffffffffc3defad 0x2fffffffff0f7beb 0xfffffffffc7fffff 0xffffffffff1fffff

def z206 : W := mkw 0x8d9d7c7d9c0da3a0 0x23675f1f670368e8 0xdf9ffc7ffc0fe3e3 0xf7e7ff1fff03f8f8

def z207 : W := mkw 0x0ed47ea41ed002d8 0x83b51fa907b400b6 0xfffe7fff1ff003ff 0xffff9fffc7fc00ff

def z208 : W := mkw 0x1fdd763480000001 0x07f75d8d20000000 0x9b99e478e0000003 0xe6e6791e38000000

def z209 : W := mkw 0x0d1d000019069000 0x034740000641a400 0x7f9f80001f8ffc03 0xdfe7e00007e3ff00

def z210 : W := mkw 0x1fffa4001be6d850 0x47ffe90006f9b614 0xffffe4001fffffff 0xfffff90007ffffff

def z211 : W := mkw 0x1ffffe801ed002d8 0x87ffffa007b400b6 0xffffff801ff003ff 0xffffffe007fc00ff

def z212 : W := mkw 0xcc14586d3d8fb7f4 0x3305161b4f63edfd 0xec1e787f1f8fffff 0x7b079e1fc7e3ffff

def z213 : W := mkw 0x4fc97658bbcb15f4 0x93f25d962ef2c57d 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z214 : W := mkw 0x61aba55be1ab7d74 0x186ae956f86adf5d 0xfb9fe47ff38fffff 0xfee7f91ffce3ffff

def z215 : W := mkw 0x1e7680001a64c800 0x479da00006993200 0x046600000c70e000 0x01198000031c3800

def z216 : W := mkw 0x1f7f88801f76da08 0x47dfe22007ddb682 0xffff9f801fffff1f 0xffffe7e007ffffc7

def z217 : W := mkw 0x1fdd7e801fd692d8 0xc7f75fa007f5a4b6 0xfff87f801ff703ff 0xbffe1fe007fdc0ff

def z218 : W := mkw 0x0022810240204800 0x0008a04090081200 0xe4679fc7ec78fc02 0xf919e7f1fb1e3f00

def z219 : W := mkw 0x000000001b469000 0x4000000006d1a400 0x0000000013870000 0x0000000004e1c000

def z220 : W := mkw 0x0e4008801ed002d8 0x8390022007b400b6 0x7fe000001ff003ff 0x9ff8000007fc00ff

def z221 : W := mkw 0x00a2f736c0000001 0x0028bdcdb0000000 0x8467ffffe0000002 0xe119fffff8000000

def z222 : W := mkw 0x0c00500018000080 0x0300140006000020 0x08006000100000e1 0x0200180004000038

def z223 : W := mkw 0x202288c124386f0c 0x0808a230490e1bc3 0x646780000c78ff1e 0xd919e000031e3fc7

def z224 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x8406787f0c00e3e0 0x21019e1fc30038f8

def z225 : W := mkw 0x4fc97e90bfd216dc 0x93f25fa42ff485b7 0xffe1ff80fff01fff 0xbff87fe03ffc07ff

def z226 : W := mkw 0x41090010a1021404 0x1042400428408501 0x00018000e0001c00 0x0000600038000700

def z227 : W := mkw 0x1fdd76349b469001 0x47f75d8d26d1a400 0x1b98603813870001 0x06e6180e04e1c000

def z228 : W := mkw 0x136b800003625800 0x44dae00000d89600 0x33e1800003f01c00 0x8cf8600000fc0700

def z229 : W := mkw 0x1f5d00001b66d800 0x47d7400006d9b600 0x7b9800001ffffc01 0x1ee6000007ffff00

def z230 : W := mkw 0x0ec0760000800050 0x03b01d8000200014 0xffe07f80138003ff 0xbff81fe004e000ff

def z231 : W := mkw 0x0000004020080504 0x0000001008020141 0xe0018440e0081f1e 0xf8006110380207c7

def z232 : W := mkw 0x8c36d96f5c0da3a0 0x230db65bd70368e8 0xcc7ffffffc0fe3e3 0xf31fffffff03f8f8

def z233 : W := mkw 0x0000580004000280 0x00001600010000a0 0x80007800000003e0 0x20001e00000000f8

def z234 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x1b99e078f38f1ce1 0x46e6781e3ce3c738

def z235 : W := mkw 0xaef6ffef7efdeffc 0xabbdbffbdfbf7bff 0xffffffffffffffff 0xffffffffffffffff

def z236 : W := mkw 0x1f7fd336c0000001 0x07dff4cdb0000000 0x047f9bffe0000000 0x411fe6fff8000000

def z237 : W := mkw 0x3e7689835e74ea08 0x4f9da260d79d3a82 0x04661b870c70e000 0x011986e1c31c3800

def z238 : W := mkw 0x1e5400001a448000 0x4795000006912000 0x0000000000000000 0x0000000000000000

def z239 : W := mkw 0x1ffff736d8048001 0x07fffdcdb6012000 0xdffffffffc0fe003 0xf7ffffffff03f800

def z240 : W := mkw 0x13eba712c3625801 0x44fae9c4b0d89600 0x33e18780e3f01c00 0x8cf861e038fc0700

def z241 : W := mkw 0x00802c8004900258 0x00200b2001240096 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z242 : W := mkw 0x80000849040923a0 0x20000212410248e8 0x00000000000003e0 0x00000000000000f8

def z243 : W := mkw 0x4000000021821454 0x1000000008608515 0x2000000003801c1c 0x0800000000e00707

def z244 : W := mkw 0x2022810340206800 0x0808a040d0081a00 0x000600070000e000 0x00018001c0003800

def z245 : W := mkw 0x0ee2fe801ef04ad8 0x83b8bfa007bc12b6 0xffe7ff801ff8ffff 0xfff9ffe007fe3fff

def z246 : W := mkw 0xcc947c7dbc8da7f4 0x33251f1f6f2369fd 0xcc1e7c7ffc0fe3ff 0x73079f1fff03f8ff

def z247 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x17e79f87e0000000 0x85f9e7e1f8000000

def z248 : W := mkw 0x11bfa536c0000001 0x046fe94db0000000 0x9b9fe47fe0000003 0xe6e7f91ff8000000

def z249 : W := mkw 0x1ffff736c1021001 0x07fffdcdb0408400 0xfffffffff38f1c03 0xfffffffffce3c700

def z250 : W := mkw 0x1ffff736da64c801 0x47fffdcdb6993200 0x9fffffffec70e003 0xe7fffffffb1c3800

def z251 : W := mkw 0x41892cd8bfdb17fc 0x90624b362ff6c5ff 0xfb99e478ffff1fff 0xfee6791e3fffc7ff

def z252 : W := mkw 0x1fffff36dc000281 0x07ffffcdb70000a0 0xdffffffffc0003e3 0xf7ffffffff0000f8

def z253 : W := mkw 0x4fc976189bc310f0 0x93f25d8626f0c43c 0x1b986038138700e1 0x06e6180e04e1c038

def z254 : W := mkw 0x8ed47e6d1c0da3a0 0x23b51f9b470368e8 0xdffe7fff1c0fe3e3 0xf7ff9fffc703f8f8

def z255 : W := mkw 0x5f7f8058bb6fdd24 0x57dfe0162edbf749 0x7fff8078fffffc03 0xdfffe01e3fffff00

def z256 : W := mkw 0x1ffff60000000000 0x07fffd8000000000 0x9fffff8000000003 0xe7ffffe000000000

def z257 : W := mkw 0x2022814360286d04 0x0808a050d80a1b41 0x84679fc7e008fc02 0xe119e7f1f8023f00

def z258 : W := mkw 0x0000010240000000 0x0000004090000000 0x80001fc7e0000000 0x200007f1f8000000

def z259 : W := mkw 0x010900001b66d800 0x4042400006d9b600 0x7b9980001ffffc03 0xdee6600007ffff00

def z260 : W := mkw 0x80807f7fc40923a1 0x20201fdff10248e8 0x80007fffe00003e0 0x20001ffff80000f8

def z261 : W := mkw 0x20a2ffc364b86fdc 0x8828bff0d92e1bf7 0xe467ffc7ec78fffe 0xf919fff1fb1e3fff

def z262 : W := mkw 0x1ffff736db469001 0x47fffdcdb6d1a400 0x9ffffffff3870003 0xe7fffffffce1c000

def z263 : W := mkw 0x5fffa458bbefdd74 0x57ffe9162efbf75d 0xffffe478ffffffff 0xfffff91e3fffffff

def z264 : W := mkw 0x01897736c0000001 0x00625dcdb0000000 0x9b99ffffe0000003 0xe6e67ffff8000000

def z265 : W := mkw 0x136b80001b66d800 0x44dae00006d9b600 0x73e180001ffffc00 0x9cf8600007ffff00

def z266 : W := mkw 0x8c1458651c0ca380 0x23051619470328e0 0xc40618470c08e302 0x71018611c30238c0

def z267 : W := mkw 0x8014586d040da3a0 0x2005161b410368e8 0x801e787f000fe3e0 0x60079e1fc003f8f8

def z268 : W := mkw 0x20a2adc364b86f5c 0x0828ab70d92e1bd7 0xffe7ffc7fff8ffff 0xfff9fff1fffe3fff

def z269 : W := mkw 0x200008c12418270c 0x08000230490609c3 0x000000000000031c 0x00000000000000c7

def z270 : W := mkw 0x0022810240000000 0x0008a04090000000 0x00618780e0000000 0x801861e038000000

def z271 : W := mkw 0x1e7680001a64c800 0x479da00006993200 0x646780000c78fc02 0xd919e000031e3f00

def z272 : W := mkw 0x0c14502418048000 0x0305140906012000 0xcc1e787f1c0fe003 0x73079e1fc703f800

def z273 : W := mkw 0x5fdd2458bbcf9574 0x57f749162ef3e55d 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z274 : W := mkw 0x0fc97e801fd212d8 0x83f25fa007f484b6 0xfff9ff801fff1fff 0xfffe7fe007ffc7ff

def z275 : W := mkw 0x0000084104082300 0x00000210410208c0 0xc40618470c08e302 0x71018611c30238c0

def z276 : W := mkw 0x1fffa6801bf6d858 0xc7ffe9a006fdb616 0x7fff87801ffffc1f 0xdfffe1e007ffff07

def z277 : W := mkw 0xc19d247da18fb574 0x3067491f6863ed5d 0xfb9fe47ff38fffff 0xfee7f91ffce3ffff

def z278 : W := mkw 0x41892410a1821454 0x1062490428608515 0xbb99e478e3801c1f 0xeee6791e38e00707

def z279 : W := mkw 0x60a2addbe4b96f7c 0x1828ab76f92e5bdf 0xe467ffffec78fffe 0xf919fffffb1e3fff

def z280 : W := mkw 0x0ec07ec03ed807dc 0x83b01fb00fb601f7 0xffe1ffc0fff81fff 0xfff87ff03ffe07ff

def z281 : W := mkw 0x0000084124082704 0x00000210490209c1 0xe4079c47ec08ff1e 0xf901e711fb023fc7

def z282 : W := mkw 0x111d000001069000 0x444740000041a400 0x0018000000070000 0x000600000001c000

def z283 : W := mkw 0x0022810240000000 0x0008a04090000000 0x04661b8700000000 0x011986e1c0000000

def z284 : W := mkw 0x8c1458251c04a280 0x23051609470128a0 0x8c1e787f0c00e003 0x63079e1fc3003800

def z285 : W := mkw 0x6febffdbfffb7ffc 0x9bfafff6fffedfff 0xffffffffffffffff 0xffffffffffffffff

def z286 : W := mkw 0x801400250004a000 0x2005000940012800 0x000600070000e000 0x00018001c0003800

def z287 : W := mkw 0x0c0058001c000280 0x03001600070000a0 0x040018000c000000 0x0100060003000000

def z288 : W := mkw 0x2ee2ffc37ef86fdc 0x8bb8bff0dfbe1bf7 0xffe7ffc7fff8ffff 0xfff9fff1fffe3fff

def z289 : W := mkw 0x20a2fff7e4386f0d 0x0828bffdf90e1bc3 0xe467ffffec78ff1e 0xf919fffffb1e3fc7

def z290 : W := mkw 0xbf7fd9ef7f7fffac 0x6fdff67bdfdfffeb 0xffffffffffffffff 0xffffffffffffffff

def z291 : W := mkw 0x0000004020080504 0x0000001008020141 0x80000440e000031c 0x20000110380000c7

def z292 : W := mkw 0x02c02e801ed002d8 0x80b00ba007b400b6 0x73e007801ff003fc 0x9cf801e007fc00ff

def z293 : W := mkw 0x0c1400001b66d800 0x4305000006d9b600 0x6c1e00001ffffc03 0x5b07800007ffff00

def z294 : W := mkw 0x02c02e8006d00258 0x80b00ba001b40096 0xf7e01f800ff0031e 0xbdf807e003fc00c7

def z295 : W := mkw 0x0e4000001a400000 0x0390000006900000 0x046000000c700000 0x01180000031c0000

def z296 : W := mkw 0x0109001080000000 0x0042400420000000 0x00198078e0000000 0x4006601e38000000

def z297 : W := mkw 0x9fdd7e7d9c0da3a1 0x27f75f9f670368e8 0xdf9e787f1c0fe3e3 0x77e79e1fc703f8f8

def z298 : W := mkw 0x1ffff736c3625801 0x47fffdcdb0d89600 0xbfffffffe3f01c03 0xeffffffff8fc0700

def z299 : W := mkw 0x1fffffb6c4100209 0x07ffffedb1040082 0xffffffffec70031f 0xfffffffffb1c00c7

def z300 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x041e187f0c0fe000 0x4107861fc303f800

def z301 : W := mkw 0x3ffffff7ff7eff0d 0x4ffffffdffdfbfc3 0xffffffffffffff1f 0xffffffffffffffc7

def z302 : W := mkw 0xa02289cb7c3defac 0x2808a272df0f7beb 0xe4679fc7fc7ffffe 0xf919e7f1ff1fffff

def z303 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x64661b870c78ff1c 0x191986e1c31e3fc7

def z304 : W := mkw 0x0c0058801ed002d8 0x8300162007b400b6 0xec0078001ff003ff 0x3b001e0007fc00ff

def z305 : W := mkw 0xc1892c59bd8fb7f4 0x30624b166f63edfd 0xfb99e478ff8fffff 0xfee6791e3fe3ffff

def z306 : W := mkw 0x0000080104002200 0x0000020041000880 0x040618070c00e000 0x01018601c3003800

def z307 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x60618780ec78ff1c 0x981861e03b1e3fc7

def z308 : W := mkw 0x0c36d12640000000 0x030db44990000000 0x8c7fffffe0000003 0xe31ffffff8000000

def z309 : W := mkw 0x0c0058481c0903a0 0x03001612070240e8 0xcc1878781c0f03e3 0x73061e1e0703c0f8

def z310 : W := mkw 0x40802458a0890574 0x102009162822415d 0xe001e478e0081ffe 0xf800791e380207ff

def z311 : W := mkw 0x5fdd24189bc79070 0x57f7490626f1e41c 0x1b986038138700e1 0x06e6180e04e1c038

def z312 : W := mkw 0x01aba512c0000000 0x006ae944b0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z313 : W := mkw 0x0000088004100208 0x0000022001040082 0x80001f800000031c 0x200007e0000000c7

def z314 : W := mkw 0x0fc9761080000000 0x03f25d8420000000 0x9ff9fff8e0000003 0xe7fe7ffe38000000

def z315 : W := mkw 0x9f7fd86d1c0da3a0 0x27dff61b470368e8 0xdffff87f1c0fe3e3 0xf7fffe1fc703f8f8

def z316 : W := mkw 0x8000586d040923a0 0x2000161b410248e8 0x8000787f000003e0 0x20001e1fc00000f8

def z317 : W := mkw 0x336b818263725c0c 0x4cdae06098dc9703 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z318 : W := mkw 0x3ffffff7e4386f0d 0x0ffffffdf90e1bc3 0xffffffffec78ff1f 0xfffffffffb1e3fc7

def z319 : W := mkw 0x0ec076001ac000d0 0x83b01d8006b00034 0x9fe07f80138000e3 0xa7f81fe004e00038

def z320 : W := mkw 0x61aba592e1b25c5c 0x186ae964b86c9717 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z321 : W := mkw 0x51bfa458a1afdd74 0x546fe916286bf75d 0xfb9fe478f38fffff 0xfee7f91e3ce3ffff

def z322 : W := mkw 0x8ed47e6d1ecda3f0 0xa3b51f9b47b368fc 0xdf9e787f1f8fe3e3 0x77e79e1fc7e3f8f8

def z323 : W := mkw 0x202289c36418270c 0x0808a270d90609c3 0x84679fc7e000031e 0xe119e7f1f80000c7

def z324 : W := mkw 0x0e405a801ed002d8 0x839016a007b400b6 0x64601b801ff003fc 0x191806e007fc00ff

def z325 : W := mkw 0x8014006d000da120 0x2005001b40036848 0xc81e607f100fe3e3 0x7207981fc403f8f8

def z326 : W := mkw 0x1f7f80403b6edd04 0x47dfe0100edbb741 0xffff8440ffffff1f 0xffffe1103fffffc7

def z327 : W := mkw 0x0000004100082100 0x0000001040020840 0x000600470008e000 0x40018011c0023800

def z328 : W := mkw 0x113f800000000000 0x044fe00000000000 0x001f800000000000 0x4007e00000000000

def z329 : W := mkw 0x0e4008801e500208 0x0390022007940082 0xffe01f801ff0031f 0xbff807e007fc00c7

def z330 : W := mkw 0x00000880049002d8 0x80000220012400b6 0x00000000000003fc 0x00000000000000ff

def z331 : W := mkw 0x200008c13ef86fdc 0x880002304fbe1bf7 0x600000001ff8fffc 0x1800000007fe3fff

def z332 : W := mkw 0x5ffff77efbefdd75 0x57fffddfbefbf75d 0xffffffffffffffff 0xffffffffffffffff

def z333 : W := mkw 0x8000586d040923a0 0x2000161b410248e8 0xc406787f0c08e3e2 0x71019e1fc30238f8

def z334 : W := mkw 0x8c14502c180580a0 0x2305140b06016028 0x4c1e60381c0fe0e3 0x5307980e0703f838

def z335 : W := mkw 0x600008c925bb7f7c 0x18000232496edfdf 0x600000001ffffffc 0x1800000007ffffff

def z336 : W := mkw 0x7fffaddbffffff7c 0x5fffeb76ffffffdf 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x000000001a400000 0x0000000006900000 0x600000001ff00000 0x1800000007fc0000

def z338 : W := mkw 0x2022898344306a08 0x0808a260d10c1a82 0x84679fc7ec70e002 0xe119e7f1fb1c3800

def z339 : W := mkw 0x8c14506c180d81a0 0x2305141b06036068 0xc8186078100f03e3 0x7206181e0403c0f8

def z340 : W := mkw 0x41892c59a58b3774 0x10624b166962cddd 0xff9ffc7fff8fffff 0xffe7ff1fffe3ffff

def z341 : W := mkw 0x113f80001b66d800 0x444fe00006d9b600 0x601f80001ffffc00 0x5807e00007ffff00

def z342 : W := mkw 0x2000004120286d04 0x08000010480a1b41 0x000000000008fc00 0x0000000000023f00

def z343 : W := mkw 0x61892cd9a5bb7f7c 0x18624b36696edfdf 0xfb99e478ffffffff 0xfee6791e3fffffff

def z344 : W := mkw 0x13eba68003f25858 0xc4fae9a000fc9616 0x33e1878003f01c1c 0x8cf861e000fc0707

def z345 : W := mkw 0x2022810260204c04 0x0808a04098081301 0x00018000e0001c00 0x0000600038000700

def z346 : W := mkw 0x1f7fd32640000001 0x07dff4c990000000 0x1fff9b8700000003 0xc7ffe6e1c0000000

def z347 : W := mkw 0x4189241881831070 0x106249062060c41c 0x9b99e478f38700e3 0xe6e6791e3ce1c038

def z348 : W := mkw 0x0022894344082300 0x0008a250d10208c0 0xc4679fc7ec08e302 0xf119e7f1fb0238c0

def z349 : W := mkw 0x1e76d32640000001 0x079db4c990000000 0x8c7e7bff00000003 0x631f9effc0000000

def z350 : W := mkw 0x0e4000001b66d800 0x4390000006d9b600 0x7fe000001ffffc03 0x9ff8000007ffff00

def z351 : W := mkw 0x0080244020880554 0x0020091008220155 0xfb81e440f3881fff 0xfee079103ce207ff

def z352 : W := mkw 0x1e76800000000000 0x079da00000000000 0x0466000000000000 0x0119800000000000

def z353 : W := mkw 0x4000004820890574 0x100000120822415d 0x00000000000003fc 0x00000000000000ff

def z354 : W := mkw 0x1e76d32640000001 0x079db4c990000000 0x84679fc7e0000002 0xe119e7f1f8000000

def z355 : W := mkw 0x1fffffb6c49002d9 0x87ffffedb12400b6 0x9fffffffe00003ff 0xe7fffffff80000ff

def z356 : W := mkw 0x0109000001021000 0x0042400000408400 0x00198000000f1c00 0x400660000003c700

def z357 : W := mkw 0x0ec076001ac000d0 0x83b01d8006b00034 0xfb806400138003ff 0xbee0190004e000ff

def z358 : W := mkw 0x913f806d012ff920 0x644fe01b404bfe48 0x001f807f000ffc00 0x4007e01fc003ff00

def z359 : W := mkw 0xac1458ed3c3defac 0x2b05163b4f0f7beb 0xec1e787f1c7fffff 0x7b079e1fc71fffff

def z360 : W := mkw 0x1febff92ded002d9 0x87faffe4b7b400b6 0xffe1ff80fff003ff 0xbff87fe03ffc00ff

def z361 : W := mkw 0x1fffffb6dff6dad9 0xc7ffffedb7fdb6b6 0xffffffffffffffff 0xffffffffffffffff

def z362 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x7b986038138f1ffd 0x1ee6180e04e3c7ff

def z363 : W := mkw 0x000000000126d800 0x400000000049b600 0x00000000000ffc00 0x000000000003ff00

def z364 : W := mkw 0x112b800001225800 0x444ae00000489600 0x0001800000001c00 0x0000600000000700

def z365 : W := mkw 0x01090040210a1504 0x0042401008428541 0xfb998440f38f1f1f 0xfee661103ce3c7c7

def z366 : W := mkw 0x9f5d586d1f4fb3a0 0x67d7561b47d3ece8 0xdf9e787f1f8fe3e3 0x77e79e1fc7e3f8f8

def z367 : W := mkw 0x0000008000100008 0x0000002000040002 0x206007800070001c 0x881801e0001c0007

def z368 : W := mkw 0x400008c83fdb17fc 0x900002320ff6c5ff 0x600000001fff1ffc 0x1800000007ffc7ff

def z369 : W := mkw 0x3e7689c37e7cef0c 0x4f9da270df9f3bc3 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z370 : W := mkw 0x1f7fd02400000000 0x07dff40900000000 0x9ffff87f00000003 0xe7fffe1fc0000000

def z371 : W := mkw 0x13eba712c0000001 0x04fae9c4b0000000 0x97e79fc7e0000002 0xe5f9e7f1f8000000

def z372 : W := mkw 0x8e545aa51e54a288 0xa39516a9479528a2 0x04661b870c70e000 0x011986e1c31c3800

def z373 : W := mkw 0x8000502c000100a0 0x2000140b00004028 0x00006038000000e0 0x0000180e00000038

def z374 : W := mkw 0x0c1458241c000280 0x03051609070000a0 0xcc1e787f1c0003e3 0x73079e1fc70000f8

def z375 : W := mkw 0x20807fc3649827dc 0x88201ff0d92609f7 0x80007fc7e00003fc 0x20001ff1f80000ff

def z376 : W := mkw 0x0ee2f70240000000 0x03b8bdc090000000 0x9fe7ffc7e0000003 0xe7f9fff1f8000000

def z377 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x8818787f100703e1 0x22061e1fc401c0f8

def z378 : W := mkw 0x0000084104082300 0x00000210410208c0 0x8000184700000300 0x20000611c00000c0

def z379 : W := mkw 0x2000098344102208 0x08000260d1040882 0x00001b8700000000 0x000006e1c0000000

def z380 : W := mkw 0x513f8058a12fdd24 0x544fe016284bf749 0x001f8078e00ffc00 0x4007e01e3803ff00

def z381 : W := mkw 0x60802ddbe499277c 0x18200b76f92649df 0x80007fffe00003fc 0x20001ffff80000ff

def z382 : W := mkw 0x1e76dba65e500289 0x879db6e9979400a2 0x04661b870c700000 0x011986e1c31c0000

def z383 : W := mkw 0x113f8136c0000001 0x044fe04db0000000 0x847f9fffe0000002 0xe11fe7fff8000000

def z384 : W := mkw 0x9ffff77fc00da121 0x27fffddff0036848 0x9fffffffe00fe003 0xe7fffffff803f800

def z385 : W := mkw 0x13ebf736c0000001 0x04fafdcdb0000000 0x93e1ffffe0000000 0xa4f87ffff8000000

def z386 : W := mkw 0x1262830240000001 0x0498a0c090000000 0x0060038000000000 0x001800e000000000

def z387 : W := mkw 0x200008c124386f0c 0x08000230490e1bc3 0xe40618470c78ff1e 0x79018611c31e3fc7

def z388 : W := mkw 0x0000000020000404 0x0000000008000101 0x20018400e0001c1c 0x8800610038000707

def z389 : W := mkw 0x5ffffed8bfffdffc 0xd7ffffb62ffff7ff 0xfffffff8ffffffff 0xfffffffe3fffffff

def z390 : W := mkw 0x0f4900001b421000 0x03d2400006d08400 0x7ff980001fff1c03 0xdffe600007ffc700

def z391 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x33998478e38f1c1c 0xcce6611e38e3c707

def z392 : W := mkw 0x41090058a10b1524 0x104240162842c549 0xc819e078f00f1fe3 0x7206781e3c03c7f8

def z393 : W := mkw 0x0ec07e801ff6dad8 0xc3b01fa007fdb6b6 0xffe07f801fffffff 0xbff81fe007ffffff

def z394 : W := mkw 0x4ec07ed8bed907fc 0x93b01fb62fb641ff 0xffe07ff8fff003ff 0xbff81ffe3ffc00ff

def z395 : W := mkw 0x11bff736c0000001 0x046ffdcdb0000000 0x801fffffe0000000 0x6007fffff8000000

def z396 : W := mkw 0x0000000000800050 0x0000000000200014 0x60000000138003fc 0x1800000004e000ff

def z397 : W := mkw 0x1ffff77ec0090121 0x07fffddfb0024048 0xdffffffff00f03e3 0xf7fffffffc03c0f8

def z398 : W := mkw 0x313f8143612efd04 0x4c4fe050d84bbf41 0x001f8047e00ffc00 0x4007e011f803ff00

def z399 : W := mkw 0x0109000001021000 0x0042400000408400 0x1b98000013870001 0x06e6000004e1c000

def z400 : W := mkw 0x313f8177e0286d05 0x0c4fe05df80a1b41 0x001f807fe008fc00 0x4007e01ff8023f00

def z401 : W := mkw 0x4ec07ec83fdb17fc 0x93b01fb20ff6c5ff 0xffe07f801fff1fff 0xbff81fe007ffc7ff

def z402 : W := mkw 0x80000049000da120 0x2000001240036848 0x00000000000fe000 0x000000000003f800

def z403 : W := mkw 0x1fdd7eb49ed002d9 0x87f75fad27b400b6 0xfff87fb81ff003ff 0xbffe1fee07fc00ff

def z404 : W := mkw 0x40000048218b1574 0x100000120862c55d 0xe8186078138f1fff 0x7a06181e04e3c7ff

def z405 : W := mkw 0x00005a8004100288 0x800016a0010400a2 0x00001b8000000000 0x000006e000000000

def z406 : W := mkw 0x2022818240304808 0x0808a060900c1202 0x0060038000700000 0x001800e0001c0000

def z407 : W := mkw 0x1ef6f72640000001 0x07bdbdc990000000 0x9fe67f8700000003 0xa7f99fe1c0000000

def z408 : W := mkw 0x2000014360082504 0x08000050d8020941 0x00000047e0000000 0x00000011f8000000

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0x80018440e0000002 0xe000611038000000

def z410 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x8019e478e00f1ffc 0x6006791e3803c7ff

def z411 : W := mkw 0x1f7f810240000000 0x07dfe04090000000 0x9fff9fc7e0000003 0xe7ffe7f1f8000000

def z412 : W := mkw 0x0000004820090524 0x0000001208024149 0xe819e478f00f1fff 0xfa06791e3c03c7ff

def z413 : W := mkw 0x1ef6f736c0000001 0x07bdbdcdb0000000 0x84667fffe0000000 0x21199ffff8000000

def z414 : W := mkw 0x336b89c3677a7f0c 0x4cdae270d9de9fc3 0xf7e79fc7eff8ff1e 0xfdf9e7f1fbfe3fc7

def z415 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x73818400f38f1ffc 0x9ce061003ce3c7ff

def z416 : W := mkw 0x5ffffffeffdb17fd 0x97ffffffbff6c5ff 0xffffffffffff1fff 0xffffffffffffc7ff

def z417 : W := mkw 0x8014002c00058020 0x2005000b00016008 0x0018003800070000 0x0006000e0001c000

def z418 : W := mkw 0x8c947c6d1c8da3f0 0x23251f1b472368fc 0xff9e7c7f1f8fe3ff 0xffe79f1fc7e3f8ff

def z419 : W := mkw 0xc00008493d8fb7f4 0x300002124f63edfd 0x600000001f8ffffc 0x1800000007e3ffff

def z420 : W := mkw 0x00807e801ed002d8 0x80201fa007b400b6 0xe0007f801ff003fc 0x38001fe007fc00ff

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x8406184700000002 0x61018611c0000000

def z422 : W := mkw 0x3f7f88c13f7eff0c 0x4fdfe2304fdfbfc3 0x7fff80001fffff1f 0xdfffe00007ffffc7

def z423 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x3bf9800013f71c01 0x8efe600004fdc700

def z424 : W := mkw 0x1f7f88801ff6dad8 0xc7dfe22007fdb6b6 0x7fff80001fffffff 0xdfffe00007ffffff

def z425 : W := mkw 0x2000088104306a08 0x08000220410c1a82 0x000000000c70e000 0x00000000031c3800

def z426 : W := mkw 0x0000084104082300 0x00000210410208c0 0x400000000c08e300 0x10000000030238c0

def z427 : W := mkw 0x1fdd763480000001 0x07f75d8d20000000 0x9f9e787f00000003 0x67e79e1fc0000000

def z428 : W := mkw 0x1262800002604800 0x4498a00000981200 0x0060000000700000 0x00180000001c0000

def z429 : W := mkw 0x1f5d00001b469000 0x47d7400006d1a400 0x7b998000138f1c03 0xdee6600004e3c700

def z430 : W := mkw 0x8c1408491c0da3a0 0x23050212470368e8 0x4c1e00001c0fe3e3 0x530780000703f8f8

def z431 : W := mkw 0x1f7f80001a64c800 0x47dfe00006993200 0x1fff80000c70e003 0xc7ffe000031c3800

def z432 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x1b9fe07fe0000001 0x46e7f81ff8000000

def z433 : W := mkw 0x0e4058001e400280 0x03901600079000a0 0xffe078001ff003e3 0xbff81e0007fc00f8

def z434 : W := mkw 0x0022814260080504 0x0008a05098020141 0xe4679fc7e0081f1e 0xf919e7f1f80207c7

def z435 : W := mkw 0x53eba712e1821455 0x14fae9c4b8608515 0x33e18780e3801c1c 0x8cf861e038e00707

def z436 : W := mkw 0x0000000800010020 0x0000000200004008 0x08186038100700e1 0x0206180e0401c038

def z437 : W := mkw 0x1f7f88411f6efb00 0x47dfe21047dbbec0 0xffff98471fffff03 0xffffe611c7ffffc0

def z438 : W := mkw 0x103680000024c800 0x440da00000093200 0x000600000000e000 0x0001800000003800

def z439 : W := mkw 0x0ec0760000000000 0x03b01d8000000000 0x1b80600000000001 0x06e0180000000000

def z440 : W := mkw 0x5ffff77ee10b1525 0x17fffddfb842c549 0x9fffffffe00f1c03 0xe7fffffff803c700

def z441 : W := mkw 0x0ed4762400000000 0x03b51d8900000000 0x9ffe7fff00000003 0xe7ff9fffc0000000

def z442 : W := mkw 0x8000582504002280 0x20001609410008a0 0x0000180700000000 0x00000601c0000000

def z443 : W := mkw 0x5fdd767ca18b1575 0x17f75d9f2862c55d 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z444 : W := mkw 0x0c807c001c8002d0 0x03201f00072000b4 0xff807c001f8003ff 0xbfe01f0007e000ff

def z445 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x047f80000c7ffc00 0x411fe000031fff00

def z446 : W := mkw 0xdffffc7dbfeffff4 0x77ffff1f6ffbfffd 0xfffffc7fffffffff 0xffffff1fffffffff

def z447 : W := mkw 0x2c3689c37c3cef0c 0x0b0da270df0f3bc3 0xec7f9fc7fc7fff1f 0xfb1fe7f1ff1fffc7

def z448 : W := mkw 0x00802c801ed002d8 0x80200b2007b400b6 0xfb8064001ff003ff 0xbee0190007fc00ff

def z449 : W := mkw 0x9d3fd97fdc0da3a1 0x274ff65ff70368e8 0xcc1ff87ffc0fe3e3 0x7307fe1fff03f8f8

def z450 : W := mkw 0x000008c104182308 0x00000230410608c2 0xe4661fc70c78e31e 0xf91987f1c31e38c7

def z451 : W := mkw 0x5fffa410bbe6dc54 0x57ffe9042ef9b715 0x7fff8400fffffc1f 0xdfffe1003fffff07

def z452 : W := mkw 0x8ec07ec91edda3f8 0xa3b01fb247b768fe 0xffe07f801fffe3ff 0xbff81fe007fff8ff

def z453 : W := mkw 0x0240000002400000 0x0090000000900000 0x33e0000003f00000 0x8cf8000000fc0000

def z454 : W := mkw 0x1f7f8136c0000001 0x07dfe04db0000000 0x1fff807fe0000003 0xc7ffe01ff8000000

def z455 : W := mkw 0x0000004800090120 0x0000001200024048 0x40000000100f03e0 0x100000000403c0f8

def z456 : W := mkw 0x9fdd763c980580a1 0x27f75d8f26016028 0x1b986038100700e1 0x06e6180e0401c038

def z457 : W := mkw 0x9f7f88491f6ffba0 0x67dfe21247dbfee8 0x7fff80001fffffe3 0xdfffe00007fffff8

def z458 : W := mkw 0x0022800000000000 0x0008a00000000000 0x0467800000000002 0xc119e00000000000

def z459 : W := mkw 0x200009c364386f0c 0x08000270d90e1bc3 0xe0001fc7ec78ff1c 0x380007f1fb1e3fc7

def z460 : W := mkw 0x0c3680001824c800 0x030da00006093200 0x6c7f80001c7ffc03 0xdb1fe000071fff00

def z461 : W := mkw 0x1ffff6001b66d800 0x47fffd8006d9b600 0xffffff801ffffc03 0xffffffe007ffff00

def z462 : W := mkw 0x136b800000000000 0x04dae00000000000 0x13e1800000000000 0x84f8600000000000

def z463 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x9b807f80138003fd 0x26e01fe004e000ff

def z464 : W := mkw 0x1e54522400000001 0x0795148900000000 0x0000000000000000 0x0000000000000000

def z465 : W := mkw 0x800008491c0da3a0 0x20000212470368e8 0xc40618471c0fe3e2 0x71018611c703f8f8

def z466 : W := mkw 0xedbffdfffdbffffc 0x3b6fff7fff6fffff 0xffffffffffffffff 0xffffffffffffffff

def z467 : W := mkw 0x3f7f89835f76fa08 0x4fdfe260d7ddbe82 0x7fff9b871ffffc03 0xdfffe6e1c7ffff00

def z468 : W := mkw 0x000000001ac000d0 0x8000000006b00034 0x00000000138000e0 0x0000000004e00038

def z469 : W := mkw 0x200001826010040c 0x0800006098040103 0x00000780e000001c 0x000001e038000007

def z470 : W := mkw 0x0c947736c0000001 0x03251dcdb0000000 0x8c1e7fffe0000003 0x63079ffff8000000

def z471 : W := mkw 0x53eba75ae18b1575 0x14fae9d6b862c55d 0xfbf9e7f8f38f1fff 0xfefe79fe3ce3c7ff

def z472 : W := mkw 0x0000000000204800 0x0000000000081200 0x600000000c78fc00 0x18000000031e3f00

def z473 : W := mkw 0x8000586d040923a0 0x2000161b410248e8 0xc818787f100f03e3 0x72061e1fc403c0f8

def z474 : W := mkw 0x13c9261080000001 0x04f2498420000000 0x1380000000000000 0x04e0000000000000

def z475 : W := mkw 0x8ed47eac1ed582f8 0xa3b51fab07b560be 0xfff87fb81ff703ff 0xbffe1fee07fdc0ff

def z476 : W := mkw 0x8ed4762c1ac580f0 0xa3b51d8b06b1603c 0x1b986038138700e1 0x06e6180e04e1c038

def z477 : W := mkw 0x0080763480000001 0x00201d8d20000000 0x0000603800000000 0x0000180e00000000

def z478 : W := mkw 0x53eba410a3e25c54 0x54fae90428f89715 0x33e18400e3f01c1c 0x8cf8610038fc0707

def z479 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xb381e478e3801ffc 0xace0791e38e007ff

def z480 : W := mkw 0x5fdd763c81831071 0x17f75d8f2060c41c 0x1b986038138700e1 0x06e6180e04e1c038

def z481 : W := mkw 0x0189241080000000 0x0062490420000000 0x13818400e0000000 0x84e0610038000000

def z482 : W := mkw 0x40802410a0800454 0x1020090428200115 0x00000400e000001c 0x0000010038000007

def z483 : W := mkw 0x113f80000126d800 0x444fe0000049b600 0x647f80000c7ffc02 0xd91fe000031fff00

def z484 : W := mkw 0x9e76db6f5c0da3a1 0x279db6dbd70368e8 0xcc7e7bff1c0fe3e3 0x731f9effc703f8f8

def z485 : W := mkw 0x0000008002d00058 0x8000002000b40016 0x2000000003f0001c 0x0800000000fc0007

def z486 : W := mkw 0x3ffff777e0286d05 0x0ffffdddf80a1b41 0x9fffffffe008fc03 0xe7fffffff8023f00

def z487 : W := mkw 0x0109000000000000 0x0042400000000000 0x1b99800000000003 0xc6e6600000000000

def z488 : W := mkw 0x8000586d1c0da3a0 0x2000161b470368e8 0xc000787f1c0fe3e0 0x30001e1fc703f8f8

def z489 : W := mkw 0x4000000801831070 0x100000020060c41c 0x00000000138700e0 0x0000000004e1c038

def z490 : W := mkw 0x80000008180580a0 0x2000000206016028 0x00000000100700e0 0x000000000401c038

def z491 : W := mkw 0x0c00000018000000 0x0300000006000000 0x4c0000001c000003 0x1300000007000000

def z492 : W := mkw 0x0080241080000000 0x0020090420000000 0x80006478e0000000 0x2000191e38000000

def z493 : W := mkw 0x0000004800090120 0x0000001200024048 0x80006078000003e0 0x2000181e000000f8

def z494 : W := mkw 0x7fffffffe5bb7f7d 0x1ffffffff96edfdf 0xffffffffffffffff 0xffffffffffffffff

def z495 : W := mkw 0x1ffff736da400001 0x07fffdcdb6900000 0xfffffffffff00003 0xfffffffffffc0000

def z496 : W := mkw 0x0000004800090120 0x0000001200024048 0x00180078000f0000 0x4006001e0003c000

def z497 : W := mkw 0x1ffff6349b66d801 0x47fffd8d26d9b600 0x7fffe0381ffffc03 0xdffff80e07ffff00

def z498 : W := mkw 0x2c36d9e764386f0c 0x0b0db679d90e1bc3 0xec7fffffec78ff1f 0xfb1ffffffb1e3fc7

def z499 : W := mkw 0xa03689ef643def2c 0x280da27bd90f7bcb 0xe47f9fffec7fff1e 0xf91fe7fffb1fffc7

def z500 : W := mkw 0x9fffffffdedda3f9 0xa7fffffff7b768fe 0xffffffffffffe3ff 0xfffffffffffff8ff

def z501 : W := mkw 0x0189245880090120 0x0062491620024048 0xdb99e478f00f03e3 0xf6e6791e3c03c0f8

def z502 : W := mkw 0xa036816f602ded24 0x280da05bd80b7b49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z503 : W := mkw 0x0ec076801ad000d8 0x83b01da006b40036 0x3be0678013f000fd 0x8ef819e004fc003f

def z504 : W := mkw 0x0022810240000000 0x0008a04090000000 0x00078047e0000000 0x4001e011f8000000

def z505 : W := mkw 0x8c1458251c04a280 0x23051609470128a0 0xcc0678071c00e3e3 0x33019e01c70038f8

def z506 : W := mkw 0x0000000001021000 0x0000000000408400 0x60000000138f1c00 0x1800000004e3c700

def z507 : W := mkw 0x53eba458a3eb5d74 0x54fae91628fad75d 0xfbf9e478f3ff1fff 0xfefe791e3cffc7ff

def z508 : W := mkw 0x2ee2ffc364386f0c 0x0bb8bff0d90e1bc3 0xffe7ffc7ec78ff1f 0xfff9fff1fb1e3fc7

def z509 : W := mkw 0x0c14000000000000 0x0305000000000000 0x0c1e000000000003 0x4307800000000000

def z510 : W := mkw 0x4d9d747ca18b1574 0x13675d1f2862c55d 0xff9ffc7ff38f1fff 0xffe7ff1ffce3c7ff

def z511 : W := mkw 0x1ffff736c0204801 0x07fffdcdb0081200 0xffffffffec78fc03 0xfffffffffb1e3f00

def z512 : W := mkw 0x02c07e8006d002d8 0x80b01fa001b400b6 0xb3e07f8003f003fc 0xacf81fe000fc00ff

def z513 : W := mkw 0x9f5d502c1b4790a0 0x67d7540b06d1e428 0x1b986038138700e1 0x06e6180e04e1c038

def z514 : W := mkw 0x51bfa57ee18b1575 0x146fe95fb862c55d 0xfb9fe47ff38f1fff 0xfee7f91ffce3c7ff

def z515 : W := mkw 0x137f80000366d800 0x44dfe00000d9b600 0x33ff800003fffc00 0xccffe00000ffff00

def z516 : W := mkw 0x0ec07ec11ed823d8 0x83b01fb047b608f6 0xffe67fc71ff8e3ff 0xfff99ff1c7fe38ff

def z517 : W := mkw 0x21abadd3e4386f0c 0x086aeb74f90e1bc3 0xffffffffec78ff1f 0xfffffffffb1e3fc7

def z518 : W := mkw 0x41892418a1831474 0x106249062860c51d 0x3b99e438f3871cfd 0x8ee6790e3ce1c73f

def z519 : W := mkw 0x1d3f80001926d800 0x474fe0000649b600 0x4c1f80001c0ffc03 0x5307e0000703ff00

def z520 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x440618071c0fe3e0 0x11018601c703f8f8

def z521 : W := mkw 0x1f7f800001021000 0x07dfe00000408400 0x7fff8000138f1c03 0xdfffe00004e3c700

def z522 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x37e780000ff0fc00 0x8df9e00003fc3f00

def z523 : W := mkw 0xc11d007da10fb524 0x3047401f6843ed49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z524 : W := mkw 0x41090058a10b1524 0x104240162842c549 0x7b998078f38f1c03 0xdee6601e3ce3c700

def z525 : W := mkw 0x2e62db835e706a88 0x8b98b6e0d79c1aa2 0x04661b870c70e000 0x011986e1c31c3800

def z526 : W := mkw 0xcd9d7c7d9d8fb3f0 0x33675f1f6763ecfc 0xdf9e787f1f8fe3e3 0x77e79e1fc7e3f8f8

def z527 : W := mkw 0x1febf712c0000001 0x07fafdc4b0000000 0x9fe1ff80e0000003 0xa7f87fe038000000

def z528 : W := mkw 0x4080777ee0890575 0x10201ddfb822415d 0x80007fffe00003fc 0x20001ffff80000ff

def z529 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x84607f800c7003fc 0x21181fe0031c00ff

def z530 : W := mkw 0x9e76d8251e64ea80 0x679db60947993aa0 0x046618070c70e000 0x01198601c31c3800

def z531 : W := mkw 0x1fffa712db66d801 0x47ffe9c4b6d9b600 0x7fff8780fffffc03 0xdfffe1e03fffff00

def z532 : W := mkw 0x800008c91edda3f8 0xa000023247b768fe 0x600000001fffe3fc 0x1800000007fff8ff

def z533 : W := mkw 0x0109000001021000 0x0042400000408400 0x3381800003801c00 0x8ce0600000e00700

def z534 : W := mkw 0x1f7fd3265b66d801 0x47dff4c996d9b600 0x7fff9b871ffffc03 0xdfffe6e1c7ffff00

def z535 : W := mkw 0x8000006d00092120 0x2000001b40024848 0x0000007f00000000 0x0000001fc0000000

def z536 : W := mkw 0x41aba55ae18b1574 0x106ae956b862c55d 0xfffffffff38f1fff 0xfffffffffce3c7ff

def z537 : W := mkw 0x8014086d040da320 0x2005021b410368c8 0xc41e187f0c0fe302 0x7107861fc303f8c0

def z538 : W := mkw 0x0ec07e8004100208 0x03b01fa001040082 0xffe07f800c70031f 0xbff81fe0031c00c7

def z539 : W := mkw 0x0ec07736c0000001 0x03b01dcdb0000000 0x9fe07fffe0000003 0xa7f81ffff8000000

def z540 : W := mkw 0x61aba5dae1bb5d7c 0x186ae976b86ed75f 0xfbf9e7f8f3ff1fff 0xfefe79fe3cffc7ff

def z541 : W := mkw 0x202289c344386b08 0x0808a270d10e1ac2 0xc4661bc70c78e302 0x711986f1c31e38c0

def z542 : W := mkw 0x1fdd76001bc690d0 0xc7f75d8006f1a434 0x1b986000138700e1 0x06e6180004e1c038

def z543 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x60078047ec78ff1c 0x5801e011fb1e3fc7

def z544 : W := mkw 0x0c00500000000000 0x0300140000000000 0x8c00780000000003 0x23001e0000000000

def z545 : W := mkw 0x1fffa4109b66d800 0x47ffe90426d9b600 0xffffe478fffffc03 0xfffff91e3fffff00

def z546 : W := mkw 0xa00059ef641927ac 0x2800167bd90649eb 0x80007fffe00003fc 0x20001ffff80000ff

def z547 : W := mkw 0x8014086d1c0da3a0 0x2005021b470368e8 0x401e007f1c0fe3e0 0x5007801fc703f8f8

def z548 : W := mkw 0x0014002400000000 0x0005000900000000 0x001e007f00000000 0x4007801fc0000000

def z549 : W := mkw 0x1d3fd136c0000001 0x074ff44db0000000 0x8c1ff87fe0000003 0x6307fe1ff8000000

def z550 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x37e01f800ff0001c 0x8df807e003fc0007

def z551 : W := mkw 0x0e405a801e500288 0x839016a0079400a2 0xcc607b801c7003e3 0x33181ee0071c00f8

def z552 : W := mkw 0x1ef6fe801ef4cad8 0xc7bdbfa007bd32b6 0xffe67f801ff0e3ff 0xbff99fe007fc38ff

def z553 : W := mkw 0x0c807e801c9002d8 0x83201fa0072400b6 0xcc007f801c0003ff 0x33001fe0070000ff

def z554 : W := mkw 0x4109001881031020 0x104240062040c408 0x0018003800070000 0x0006000e0001c000

def z555 : W := mkw 0x01090048010b1120 0x004240120042c448 0xfb99e078138f1fe3 0xfee6781e04e3c7f8

def z556 : W := mkw 0xdfffff7ffd8fb7f5 0x37ffffdfff63edfd 0xffffffffff8fffff 0xffffffffffe3ffff

def z557 : W := mkw 0x8c947eed1c9da3f8 0xa3251fbb472768fe 0xcc1e7fff1c0fe3ff 0x73079fffc703f8ff

def z558 : W := mkw 0x13eba792c2d00059 0x84fae9e4b0b40016 0x33e18780e3f0001c 0x8cf861e038fc0007

def z559 : W := mkw 0x8c1458251c04a280 0x23051609470128a0 0x4c1e18071c0fe003 0x53078601c703f800

def z560 : W := mkw 0x513f817ee10b1525 0x144fe05fb842c549 0x001f807fe00f1c00 0x4007e01ff803c700

def z561 : W := mkw 0x0240028002500008 0x809000a000940002 0x0060038000700000 0x001800e0001c0000

def z562 : W := mkw 0x0c1458001c048280 0x03051600070120a0 0xcc1e78001c0fe3e3 0x73079e000703f8f8

def z563 : W := mkw 0x113f8136c126d801 0x444fe04db049b600 0x001f807fe00ffc00 0x4007e01ff803ff00

def z564 : W := mkw 0x4189241881831070 0x106249062060c41c 0x7b99e038138f1ce3 0xdee6780e04e3c738

def z565 : W := mkw 0x000008801ed002d8 0x8000022007b400b6 0xe4601f801ff003fe 0xb91807e007fc00ff

def z566 : W := mkw 0x0e405a801e500288 0x839016a0079400a2 0x7fe01b801ff00003 0x9ff806e007fc0000

def z567 : W := mkw 0x9ffffeed1ffffbf8 0xe7ffffbb47fffefe 0xffffffff1fffffff 0xffffffffc7ffffff

def z568 : W := mkw 0x202289c37ef86fdc 0x8808a270dfbe1bf7 0xe4679fc7fff8fffe 0xf919e7f1fffe3fff

def z569 : W := mkw 0x1febfe801ff25ad8 0xc7faffa007fc96b6 0xffe1ff801ff01fff 0xbff87fe007fc07ff

def z570 : W := mkw 0x0189241080000000 0x0062490420000000 0x1b98603800000001 0x06e6180e00000000

def z571 : W := mkw 0x112b8112c0000001 0x044ae044b0000000 0x00018000e0000000 0x0000600038000000

def z572 : W := mkw 0x000008801ff6dad8 0xc000022007fdb6b6 0x600000001ffffffc 0x1800000007ffffff

def z573 : W := mkw 0x40802458a18b1574 0x102009162862c55d 0xe0006478f38f1ffc 0x3800191e3ce3c7ff

def z574 : W := mkw 0x1fffff77c4082301 0x07ffffddf10208c0 0xdfffffffec08e303 0xf7fffffffb0238c0

def z575 : W := mkw 0x0e40000000000000 0x0390000000000000 0x1fe0000000000003 0x87f8000000000000

def z576 : W := mkw 0x0000502400000000 0x0000140900000000 0x8000787f00000000 0x20001e1fc0000000

def z577 : W := mkw 0x2ee2ff835ef06ad8 0x8bb8bfe0d7bc1ab6 0xffe67f871ff0e3ff 0xbff99fe1c7fc38ff

def z578 : W := mkw 0x0080240000800050 0x0020090000200014 0x80006400000003fc 0x20001900000000ff

def z579 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x84661fc7ec70e31c 0x211987f1fb1c38c7

def z580 : W := mkw 0x33eba792e0304c0d 0x0cfae9e4b80c1303 0x33e18780e0701c1c 0x8cf861e0381c0707

def z581 : W := mkw 0x0c14502400000000 0x0305140900000000 0x0406180700000000 0x01018601c0000000

def z582 : W := mkw 0x5f7f80483befdd74 0x57dfe0120efbf75d 0x7fff80001fffffff 0xdfffe00007ffffff

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0x6001800000081c02 0xd800600000020700

def z584 : W := mkw 0x40000048218b1574 0x100000120862c55d 0xe0018440f38f1ffe 0xf80061103ce3c7ff

def z585 : W := mkw 0x0189241080800050 0x0062490420200014 0xfb99e478f38003ff 0xfee6791e3ce000ff

def z586 : W := mkw 0x0000000003625800 0x4000000000d89600 0x2000000003f01c00 0x0800000000fc0700

def z587 : W := mkw 0x0ec024001ac00050 0x03b0090006b00014 0xffe064001ff003ff 0xbff8190007fc00ff

def z588 : W := mkw 0x800008011c04a280 0x20000200470128a0 0x000000000c00e000 0x0000000003003800

def z589 : W := mkw 0x200008c124386f0c 0x08000230490e1bc3 0xe4601f800c78ff1e 0xb91807e0031e3fc7

def z590 : W := mkw 0x8c0058491c0da3a0 0x23001612470368e8 0xcc0078001c0fe3e3 0x33001e000703f8f8

def z591 : W := mkw 0x1f7f800018048000 0x07dfe00006012000 0x5fff80001c0fe003 0xd7ffe0000703f800

def z592 : W := mkw 0x0080240000800050 0x0020090000200014 0x338004000380001c 0x8ce0010000e00007

def z593 : W := mkw 0x9f7fd02c1b67d8a0 0x67dff40b06d9f628 0x7fffe0381ffffce3 0xdffff80e07ffff38

def z594 : W := mkw 0x0022898244100208 0x0008a26091040082 0xe4679fc7ec70031e 0xf919e7f1fb1c00c7

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8006000100003e3 0x32001800040000f8

def z596 : W := mkw 0x40802458a0890574 0x102009162822415d 0xc8186478f00f03ff 0x7206191e3c03c0ff

def z597 : W := mkw 0x0ec07e801e500288 0x83b01fa0079400a2 0x9fe07f800c700003 0xa7f81fe0031c0000

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x440600000c08e002 0x5101800003023800

def z599 : W := mkw 0x0c14000018048000 0x0305000006012000 0x0818000010070001 0x020600000401c000

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x48180000100f0003 0x520600000403c000

def z601 : W := mkw 0x0c14000018048000 0x0305000006012000 0x040600000c00e000 0x0101800003003800

def z602 : W := mkw 0x2022818260304c0c 0x0808a060980c1303 0xa4679fc7e0701c1e 0xe919e7f1f81c0707

def z603 : W := mkw 0x4fc97658a18b1574 0x13f25d962862c55d 0xfff9fff8f38f1fff 0xfffe7ffe3ce3c7ff

def z604 : W := mkw 0x8c14582c1c0582a0 0x2305160b070160a8 0xcc1878381c0703e3 0x33061e0e0701c0f8

def z605 : W := mkw 0x0c14506c00090120 0x0305141b00024048 0xcc1e787f100f03e3 0x73079e1fc403c0f8

def z606 : W := mkw 0x4189241881831070 0x106249062060c41c 0xfb986438138703ff 0xbee6190e04e1c0ff

def z607 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xa0619fc7e0701f1c 0xa81867f1f81c07c7

def z608 : W := mkw 0x8c1458ed1edda3f8 0xa305163b47b768fe 0xec1e787f1fffe3ff 0x7b079e1fc7fff8ff

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x7b80000013800003 0x9ee0000004e00000

def z610 : W := mkw 0x2ec07fc37ed827dc 0x8bb01ff0dfb609f7 0xffe07fc7fff003ff 0xbff81ff1fffc00ff

def z611 : W := mkw 0x0ec07e001ec002d0 0x83b01f8007b000b4 0xdf8078001f8003e3 0x37e01e0007e000f8

def z612 : W := mkw 0x0080244800890170 0x002009120022405c 0xfb986478138f03ff 0xfee6191e04e3c0ff

def z613 : W := mkw 0x602289cb65bb7f7c 0x1808a272d96edfdf 0xe4679fc7fffffffe 0xf919e7f1ffffffff

def z614 : W := mkw 0x212b89c3653a7f0c 0x084ae270d94e9fc3 0xffff9fc7ffffff1f 0xffffe7f1ffffffc7

def z615 : W := mkw 0x20807ff7e418270d 0x08201ffdf90609c3 0x80007fffe000031c 0x20001ffff80000c7

def z616 : W := mkw 0x800008491c0da3a0 0x20000212470368e8 0xc81860781c0fe3e3 0x7206181e0703f8f8

def z617 : W := mkw 0x111d003480000001 0x0447400d20000000 0x0018003800000000 0x0006000e00000000

def z618 : W := mkw 0x22e2a78262f04c5c 0x88b8a9e098bc1317 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z619 : W := mkw 0x2e62dbc37e786f8c 0x8b98b6f0df9e1be3 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z620 : W := mkw 0x61abadd3e5ba7f5c 0x186aeb74f96e9fd7 0xf7e79fc7eff8ff1e 0xfdf9e7f1fbfe3fc7

def z621 : W := mkw 0x2e6289c37e786f0c 0x0b98a270df9e1bc3 0xffe79fc7fff8ff1f 0xfff9e7f1fffe3fc7

def z622 : W := mkw 0x2ec07ec13ef86fdc 0x8bb01fb04fbe1bf7 0xffe07f801ff8ffff 0xbff81fe007fe3fff

def z623 : W := mkw 0x80807eed049923f8 0xa0201fbb412648fe 0x80007fff000003fc 0x20001fffc00000ff

def z624 : W := mkw 0xa022d9ef64396fac 0x2808b67bd90e5beb 0xe467ffffec78fffe 0xf919fffffb1e3fff

def z625 : W := mkw 0x3f7f81437b6efd04 0x4fdfe050dedbbf41 0x7fff8047fffffc03 0xdfffe011ffffff00

def z626 : W := mkw 0x41892cd8a59b177c 0x10624b362966c5df 0xfff9fff8ffff1fff 0xfffe7ffe3fffc7ff

def z627 : W := mkw 0x8c36d86d1c2deba0 0x230db61b470b7ae8 0xec7ff87f1c7fffe3 0xfb1ffe1fc71ffff8

def z628 : W := mkw 0x0d9d743480000000 0x03675d0d20000000 0x9f9ffc7fe0000003 0xe7e7ff1ff8000000

def z629 : W := mkw 0x43c92690a3d2145c 0x90f249a428f48517 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z630 : W := mkw 0x0ec07e80049002d8 0x83b01fa0012400b6 0x9fe07f80000003ff 0xa7f81fe0000000ff

def z631 : W := mkw 0x0000004020080504 0x0000001008020141 0x6000000000081f1c 0x18000000000207c7

def z632 : W := mkw 0x200009c36418270c 0x08000270d90609c3 0xe4601fc7ec70031e 0xb91807f1fb1c00c7

def z633 : W := mkw 0x3fffffc37ffeffdc 0xcffffff0dfffbff7 0xffffffc7ffffffff 0xfffffff1ffffffff

def z634 : W := mkw 0x0189240001821050 0x0062490000608414 0xfb99e400138f1fff 0xfee6790004e3c7ff

def z635 : W := mkw 0x0000080004000200 0x0000020001000080 0xc40018000c000302 0x31000600030000c0

def z636 : W := mkw 0x2022894364286f04 0x0808a250d90a1bc1 0xc4079847ec08ff02 0x7101e611fb023fc0

def z637 : W := mkw 0x41892458a0890574 0x106249162822415d 0x9b99e478e00003ff 0xe6e6791e380000ff

def z638 : W := mkw 0x5ffff73ec1831071 0x17fffdcfb060c41c 0x9ffffffff38700e3 0xe7fffffffce1c038

def z639 : W := mkw 0x3ffffff7fef86fdd 0x8ffffffdffbe1bf7 0xfffffffffff8ffff 0xfffffffffffe3fff

def z640 : W := mkw 0x000000001a64c800 0x4000000006993200 0x000000000c70e000 0x00000000031c3800

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0x8818607800000003 0x6206181e00000000

def z642 : W := mkw 0x3ffff7b6e0304c0d 0x0ffffdedb80c1303 0xbfffffffe0701c1f 0xeffffffff81c0707

def z643 : W := mkw 0x00807600008000d0 0x80201d8000200034 0x00006000000000e0 0x0000180000000038

def z644 : W := mkw 0x1349000003421000 0x44d2400000d08400 0x1380000003800000 0x04e0000000e00000

def z645 : W := mkw 0x8c14006d180da120 0x2305001b46036848 0x4c1e007f1c0fe003 0x5307801fc703f800

def z646 : W := mkw 0x0022800000204800 0x0008a00000081200 0x000780000008fc00 0x4001e00000023f00

def z647 : W := mkw 0x0000004020080504 0x0000001008020141 0x00018040e0081c00 0x4000601038020700

def z648 : W := mkw 0xcd9d743c998790f0 0x33675d0f2661e43c 0x1b986038138700e1 0x06e6180e04e1c038

def z649 : W := mkw 0x41090058a10b1524 0x104240162842c549 0xe0198478e00f1f1e 0xf806611e3803c7c7

def z650 : W := mkw 0xcd1d587dbd0fb7a4 0x3347561f6f43ede9 0xcc1ff87ffc0fffe3 0x7307fe1fff03fff8

def z651 : W := mkw 0x9d3fd86d1d2ffba0 0x674ff61b474bfee8 0xcc1ff87f1c0fffe3 0x7307fe1fc703fff8

def z652 : W := mkw 0x0080240000000000 0x0020090000000000 0x9b80640000000003 0xa6e0190000000000

def z653 : W := mkw 0x0e4052001a400080 0x8390148006900020 0x0000000000000000 0x0000000000000000

def z654 : W := mkw 0x9f7f806d1b6ff920 0x67dfe01b46dbfe48 0x7fff807f1ffffc03 0xdfffe01fc7ffff00

def z655 : W := mkw 0x33ebafd3e4386f0d 0x0cfaebf4f90e1bc3 0xf7e79fc7ec78ff1e 0xfdf9e7f1fb1e3fc7

def z656 : W := mkw 0x2ee2ff827ef04edc 0x8bb8bfe09fbc13b7 0xffe1ff80fff01fff 0xbff87fe03ffc07ff

def z657 : W := mkw 0x0000088004100208 0x0000022001040082 0x600000000c70031c 0x18000000031c00c7

def z658 : W := mkw 0x1f5d00001b469000 0x47d7400006d1a400 0x7ff800001ff70003 0x9ffe000007fdc000

def z659 : W := mkw 0x1f5d000000000000 0x07d7400000000000 0x1b98000000000001 0x06e6000000000000

def z660 : W := mkw 0x0ec076001ac000d0 0x83b01d8006b00034 0x7fe060001ff000e3 0x9ff8180007fc0038

def z661 : W := mkw 0x4d9d2458b98f9574 0x136749162e63e55d 0xff9fe478ff8fffff 0xffe7f91e3fe3ffff

def z662 : W := mkw 0x0ec07e001c000280 0x03b01f80070000a0 0xdfe07f801c0003e3 0xb7f81fe0070000f8

def z663 : W := mkw 0x0000004000080100 0x0000001000020040 0xc000004000080302 0x70000010000200c0

def z664 : W := mkw 0x00000136c0000001 0x0000004db0000000 0x0000007fe0000000 0x0000001ff8000000

def z665 : W := mkw 0x2022898344306a08 0x0808a260d10c1a82 0xe4661f870c70e31e 0xb91987e1c31c38c7

def z666 : W := mkw 0x200008c13f7eff0c 0x480002304fdfbfc3 0x600000001fffff1c 0x1800000007ffffc7

def z667 : W := mkw 0x2022898344306a08 0x0808a260d10c1a82 0x64679b870c78fc02 0xd919e6e1c31e3f00

def z668 : W := mkw 0x41892410a1821454 0x1062490428608515 0x7b998400f38f1c1f 0xdee661003ce3c707

def z669 : W := mkw 0x8ec07eed1ed923f8 0xa3b01fbb47b648fe 0xffe07fff1ff003ff 0xbff81fffc7fc00ff

def z670 : W := mkw 0x4189241081821050 0x1062490420608414 0x1380000003800000 0x04e0000000e00000

def z671 : W := mkw 0x0c14502400000000 0x0305140900000000 0x0818603800000001 0x0206180e00000000

def z672 : W := mkw 0xcd9d747cb98f95f4 0x33675d1f2e63e57d 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z673 : W := mkw 0x43c926d8a3db157c 0x90f249b628f6c55f 0xfbf9e7f8f3ff1fff 0xfefe79fe3cffc7ff

def z674 : W := mkw 0x0c1408411c0ca300 0x03050210470328c0 0xcc1e18471c0fe303 0x73078611c703f8c0

def z675 : W := mkw 0xc0807c7da48927f4 0x30201f1f692249fd 0x80007c7fe00003fc 0x20001f1ff80000ff

def z676 : W := mkw 0x1036812640000001 0x040da04990000000 0x0006000700000000 0x00018001c0000000

def z677 : W := mkw 0x2022814360286d04 0x0808a050d80a1b41 0xe0078447e008ff1e 0xf801e111f8023fc7

def z678 : W := mkw 0x2000008020304c0c 0x08000020080c1303 0x2000000000701c1c 0x08000000001c0707

def z679 : W := mkw 0x02c0260000000000 0x00b0098000000000 0x13e0078000000000 0x84f801e000000000

def z680 : W := mkw 0x136b800003625800 0x44dae00000d89600 0x77e780000ff8fc02 0xddf9e00003fe3f00

def z681 : W := mkw 0x4fc92458bbcb1574 0x13f249162ef2c55d 0xfff9e478ffff1fff 0xfffe791e3fffc7ff

def z682 : W := mkw 0x8c14586d1f6ffba0 0x6305161b47dbfee8 0xec1e787f1fffffe3 0x7b079e1fc7fffff8

def z683 : W := mkw 0x1ffff776e0080505 0x07fffdddb8020141 0xffffffffe0081f1f 0xfffffffff80207c7

def z684 : W := mkw 0x3ffffff7e418270d 0x0ffffffdf90609c3 0x9fffffffe000031f 0xe7fffffff80000c7

def z685 : W := mkw 0x002280001b66d800 0x4008a00006d9b600 0x646780001ffffc02 0xd919e00007ffff00

def z686 : W := mkw 0x1f7f80001b469000 0x47dfe00006d1a400 0x1fff800013870003 0xc7ffe00004e1c000

def z687 : W := mkw 0x400000483befdd74 0x500000120efbf75d 0x600000001ffffffc 0x1800000007ffffff

def z688 : W := mkw 0x00807e80049002d8 0x80201fa0012400b6 0xfb807f80138003ff 0xbee01fe004e000ff

def z689 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x481860381c0fe3e1 0x1206180e0703f8f8

def z690 : W := mkw 0x8c14506d000da120 0x2305141b40036848 0x8c1e787f000fe003 0x63079e1fc003f800

def z691 : W := mkw 0x3e76dba744306a09 0x0f9db6e9d10c1a82 0x04661b870c70e000 0x011986e1c31c3800

def z692 : W := mkw 0x1fdd76349ac000d1 0x87f75d8d26b00034 0x1b986038138000e1 0x06e6180e04e00038

def z693 : W := mkw 0x1f7f800000204800 0x07dfe00000081200 0x7fff80000c78fc03 0xdfffe000031e3f00

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x646000000c700002 0x99180000031c0000

def z695 : W := mkw 0x2022814360286d04 0x0808a050d80a1b41 0x64678047ec78fc02 0xd919e011fb1e3f00

def z696 : W := mkw 0x41090058a18b1574 0x104240162862c55d 0x60198078f38f1ffc 0x5806601e3ce3c7ff

def z697 : W := mkw 0x40802448218b1574 0x102009120862c55d 0xfb806400138f1fff 0xbee0190004e3c7ff

def z698 : W := mkw 0x01892450a0080504 0x0062491428020141 0xfb99e478e0081f1f 0xfee6791e380207c7

def z699 : W := mkw 0xac36d9a75c34ea88 0x2b0db669d70d3aa2 0x04661b870c70e000 0x011986e1c31c3800

def z700 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x1b9f8000138ffc01 0x46e7e00004e3ff00

def z701 : W := mkw 0x9fffff37dc04a281 0x27ffffcdf70128a0 0x9fffffffec00e003 0xe7fffffffb003800

def z702 : W := mkw 0x1f7f80001a400000 0x07dfe00006900000 0x7fff80001ff00003 0xdfffe00007fc0000

def z703 : W := mkw 0x1ffff7b6c2d00059 0x87fffdedb0b40016 0xbfffffffe3f0001f 0xeffffffff8fc0007

def z704 : W := mkw 0xc1897c7da58b37f4 0x30625f1f6962cdfd 0xfb99fc7ff38f1fff 0xfee67f1ffce3c7ff

def z705 : W := mkw 0x1fdd763480000001 0x07f75d8d20000000 0x9ff87fb800000003 0xa7fe1fee00000000

def z706 : W := mkw 0x22e2afc366f86f5c 0x88b8abf0d9be1bd7 0xf7e79fc7eff8ff1e 0xfdf9e7f1fbfe3fc7

def z707 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xec7f9fc7fc7fff1f 0xfb1fe7f1ff1fffc7

def z708 : W := mkw 0x3fdd7ef5a4386f0d 0x0ff75fbd690e1bc3 0x7b9860380c78ff1d 0x1ee6180e031e3fc7

def z709 : W := mkw 0x0ec07e811ed022d8 0x83b01fa047b408b6 0xffe67f871ff0e3ff 0xbff99fe1c7fc38ff

def z710 : W := mkw 0x1ffff736c126d801 0x47fffdcdb049b600 0xfffffffff38ffc03 0xfffffffffce3ff00

def z711 : W := mkw 0xcd9d7c35bd86b6d4 0x33675f0d6f61adb5 0x37879c07ef80fc1c 0x8de1e701fbe03f07

def z712 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xff9e787f1f8fe3e3 0xffe79e1fc7e3f8f8

def z713 : W := mkw 0x0080244820890574 0x002009120822415d 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z714 : W := mkw 0x1f7f83025b66d801 0x47dfe0c096d9b600 0x7fff83801ffffc03 0xdfffe0e007ffff00

def z715 : W := mkw 0x1f7f80109b66d800 0x47dfe00426d9b600 0x7fff8078fffffc03 0xdfffe01e3fffff00

def z716 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x0c1e787f1c0fe0e1 0x43079e1fc703f838

def z717 : W := mkw 0x00807736db66d801 0x40201dcdb6d9b600 0xe0007ffffffffc00 0x38001fffffffff00

def z718 : W := mkw 0x936bd86d076b7ba0 0x64daf61b41dadee8 0xb3e1f87f03f01fe0 0xacf87e1fc0fc07f8

def z719 : W := mkw 0x11bff736c126d801 0x446ffdcdb049b600 0x801fffffe00ffc00 0x6007fffff803ff00

def z720 : W := mkw 0x93ebaf5bdc0da3a1 0x24faebd6f70368e8 0x53e18780fc0fe3e0 0x94f861e03f03f8f8

def z721 : W := mkw 0x1ffff736c0800051 0x07fffdcdb0200014 0x9ffffffff38000e3 0xe7fffffffce00038

def z722 : W := mkw 0xa02289cb64396fac 0x2808a272d90e5beb 0xe4679fc7ec78fffe 0xf919e7f1fb1e3fff

def z723 : W := mkw 0x1d3fd136c0000001 0x074ff44db0000000 0x8c7fffffe0000003 0xe31ffffff8000000

def z724 : W := mkw 0x61aba512e1a25c54 0x186ae944b8689715 0x33818400e3801c1c 0x8ce0610038e00707

def z725 : W := mkw 0x1e76d336c0000001 0x079db4cdb0000000 0x04661bffe0000000 0x011986fff8000000

def z726 : W := mkw 0x1e7680001b66d800 0x479da00006d9b600 0x7fe600001ffffc03 0x9ff9800007ffff00

def z727 : W := mkw 0x11abf736c0000001 0x046afdcdb0000000 0x8001ffffe0000000 0x20007ffff8000000

def z728 : W := mkw 0x0e405a801ed002d8 0x839016a007b400b6 0x7fe01b801ff003ff 0x9ff806e007fc00ff

def z729 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x9fe07f801ff003fd 0x27f81fe007fc00ff

def z730 : W := mkw 0x600008c93fffff7c 0x580002324fffffdf 0x600000001ffffffc 0x1800000007ffffff

def z731 : W := mkw 0x5e76d36e618b1575 0x179db4db9862c55d 0x64661b87138f1ffc 0x191986e1c4e3c7ff

def z732 : W := mkw 0x113f89b6ded002d9 0x844fe26db7b400b6 0x601f807ffff003fc 0x5807e01ffffc00ff

def z733 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0xffffe0781ffffc03 0xfffff81e07ffff00

def z734 : W := mkw 0x113f8136c126d801 0x444fe04db049b600 0xe47f9fffec7ffc02 0xf91fe7fffb1fff00

def z735 : W := mkw 0x0d3f80001926d800 0x034fe0000649b600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z736 : W := mkw 0x1f7f8136db66d801 0x47dfe04db6d9b600 0xffff9ffffffffc03 0xffffe7ffffffff00

def z737 : W := mkw 0x82d426ed02dda178 0xa0b509bb40b7685e 0x33fe07ff03ffe01c 0xccff81ffc0fff807

def z738 : W := mkw 0x5ef6a458baedcd74 0x57bda9162ebb735d 0x84666478ec70e3fc 0x2119991e3b1c38ff

def z739 : W := mkw 0xa0807fef649927fc 0xa8201ffbd92649ff 0x80007fffe00003fc 0x20001ffff80000ff

def z740 : W := mkw 0x0d9d7736c0000001 0x03675dcdb0000000 0x9f9fffffe0000003 0xe7e7fffff8000000

def z741 : W := mkw 0x0ed47ea41ed002d8 0x83b51fa907b400b6 0xfff87fb81ff003ff 0xbffe1fee07fc00ff

def z742 : W := mkw 0x02c02e801ed002d8 0x80b00ba007b400b6 0xfbe067801ff003ff 0xbef819e007fc00ff

def z743 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x481e607f1c0fe3e1 0x5207981fc703f8f8

def z744 : W := mkw 0x41892418a1831474 0x106249062860c51d 0xfb99e438f3871fff 0xbee6790e3ce1c7ff

def z745 : W := mkw 0x00807736c0000001 0x00201dcdb0000000 0x84607fffe0000002 0xa1181ffff8000000

def z746 : W := mkw 0x1f7fd136db66d801 0x47dff44db6d9b600 0xfffff87ffffffc03 0xfffffe1fffffff00

def z747 : W := mkw 0x713f817fe12b7d25 0x1c4fe05ff84adf49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z748 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x84679fc7ec78ff1c 0x6119e7f1fb1e3fc7

def z749 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xdffffffff00003e3 0xf7fffffffc0000f8

def z750 : W := mkw 0x0c14512640000000 0x0305144990000000 0x8c1e7fffe0000003 0x63079ffff8000000

def z751 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xdffffffff00f0003 0xf7fffffffc03c000

def z752 : W := mkw 0x1e76d32640000001 0x079db4c990000000 0x8c7fffffe0000003 0xe31ffffff8000000

def z753 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0xffff84001fffff1f 0xffffe10007ffffc7

def z754 : W := mkw 0x0ec07e909ed002d8 0x83b01fa427b400b6 0xffe07ff8fff003ff 0xbff81ffe3ffc00ff

def z755 : W := mkw 0x3f5d09c37f5eb70c 0x4fd74270dfd7adc3 0x9b981fc7f387031d 0x26e607f1fce1c0c7

def z756 : W := mkw 0xcfdd763c9bc790f0 0xb3f75d8f26f1e43c 0x1b986038138700e1 0x06e6180e04e1c038

def z757 : W := mkw 0x1ffff736dbc690d1 0xc7fffdcdb6f1a434 0x9ffffffff38700e3 0xe7fffffffce1c038

def z758 : W := mkw 0xae76dba75e74ea88 0xab9db6e9d79d3aa2 0x04661b870c70e000 0x011986e1c31c3800

def z759 : W := mkw 0x00005336c0000001 0x000014cdb0000000 0x00001bffe0000000 0x000006fff8000000

def z760 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xa4679fc7ec70ff1c 0xa919e7f1fb1c3fc7

def z761 : W := mkw 0x00802c801ed002d8 0x80200b2007b400b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z762 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xfff9e478ffff1fff 0xfffe791e3fffc7ff

def z763 : W := mkw 0x2022818260304c0c 0x0808a060980c1303 0xe4679fc7ec78fc1e 0xf919e7f1fb1e3f07

def z764 : W := mkw 0x1ffff736dbe6d851 0x47fffdcdb6f9b614 0xffffffffffffffff 0xffffffffffffffff

def z765 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xec7e787f1c7fe3e3 0xfb1f9e1fc71ff8f8

def z766 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x7b9f80001ffffc01 0x5ee7e00007ffff00

def z767 : W := mkw 0x02c02e8006d00258 0x80b00ba001b40096 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z768 : W := mkw 0x136b800003625800 0x44dae00000d89600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z769 : W := mkw 0x000000001b66d800 0x4000000006d9b600 0x7b8000001ffffc03 0x9ee0000007ffff00

def z770 : W := mkw 0x00807e80049002d8 0x80201fa0012400b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z771 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xff9ffc7ff38f1fff 0xffe7ff1ffce3c7ff

def z772 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x17ff9fffe0000000 0xc5ffe7fff8000000

def z773 : W := mkw 0x0ec07e8006d002d8 0x83b01fa001b400b6 0xbfe07f8003f003ff 0xaff81fe000fc00ff

def z774 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xffe1ff801ff81fff 0xfff87fe007fe07ff

def z775 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xffe67f801ff8e3ff 0xfff99fe007fe38ff

def z776 : W := mkw 0x1fffa512c0000000 0x07ffe944b0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z777 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x7bf980001ffffc01 0x9efe600007ffff00

def z778 : W := mkw 0x0022810240000000 0x0008a04090000000 0x8c7fffffe0000003 0xe31ffffff8000000

def z779 : W := mkw 0x010900001b66d800 0x4042400006d9b600 0x738180001ffffc00 0x9ce0600007ffff00

def z780 : W := mkw 0x8c14502c180580a0 0x2305140b06016028 0xcc1e787f1c0fe0e3 0x73079e1fc703f838

def z781 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xffe1ffc0fff003ff 0xfff87ff03ffc00ff

def z782 : W := mkw 0x600008c92499277c 0x18000232492649df 0x00000000000003fc 0x00000000000000ff

def z783 : W := mkw 0xac36d1ae7835ccac 0x2b0db46b9e0d732b 0x2879e7b8f0771cfd 0x8a1e79ee3c1dc73f

def z784 : W := mkw 0x0e4008801ed002d8 0x8390022007b400b6 0xffe01f801ff003ff 0xbff807e007fc00ff

def z785 : W := mkw 0x513f817ee12fdd25 0x544fe05fb84bf749 0x001f807fe00ffc00 0x4007e01ff803ff00

def z786 : W := mkw 0x1f7fd2001b66d800 0x47dff48006d9b600 0x7fff9b801ffffc03 0xdfffe6e007ffff00

def z787 : W := mkw 0x1ffff736c2604801 0x47fffdcdb0981200 0x9fffffffe0700003 0xe7fffffff81c0000

def z788 : W := mkw 0xe13f817fe12ffd24 0x384fe05ff84bff49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z789 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x37ff80000ffffc00 0xcdffe00003ffff00

def z790 : W := mkw 0x8c14586d1e4da3a0 0x2305161b479368e8 0xec1e787f1fffe3e3 0x7b079e1fc7fff8f8

def z791 : W := mkw 0x1ffff736c126d801 0x47fffdcdb049b600 0xffffffffec7ffc03 0xfffffffffb1fff00

def z792 : W := mkw 0x2ee2f7437ae86dd4 0x8bb8bdd0deba1b75 0x1b87e047f388fce1 0x46e1f811fce23f38

def z793 : W := mkw 0x8ed47ea41ed482d8 0xa3b51fa907b520b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z794 : W := mkw 0x0c947736c0000001 0x03251dcdb0000000 0x88187fffe0000001 0x22061ffff8000000

def z795 : W := mkw 0x1ffff736d8000001 0x07fffdcdb6000000 0xdffffffffc000003 0xf7ffffffff000000

def z796 : W := mkw 0x8014086d040da320 0x2005021b410368c8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z797 : W := mkw 0x00947736c0000001 0x00251dcdb0000000 0x801e7fffe0000000 0x60079ffff8000000

def z798 : W := mkw 0x0ec07eb49ed002d9 0x83b01fad27b400b6 0xffe07fb81ff003ff 0xbff81fee07fc00ff

def z799 : W := mkw 0x1ed47ea41ed002d9 0x87b51fa907b400b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z800 : W := mkw 0x0fdd763480000000 0x03f75d8d20000000 0x9fffffffe0000003 0xe7fffffff8000000

def z801 : W := mkw 0x0189241081821050 0x0062490420608414 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z802 : W := mkw 0x1ffff736db421001 0x07fffdcdb6d08400 0xffffffffffff1c03 0xffffffffffffc700

def z803 : W := mkw 0x8e5458ed1e5da3a8 0x2395163b479768ea 0xfffe7fff1fffe3ff 0xffff9fffc7fff8ff

def z804 : W := mkw 0x0fc97736c0000001 0x03f25dcdb0000000 0x9ff9ffffe0000003 0xe7fe7ffff8000000

def z805 : W := mkw 0x0ed47ea41ed482d8 0x83b51fa907b520b6 0xfffe7fff1fffe3ff 0xffff9fffc7fff8ff

def z806 : W := mkw 0x1f7fd12640000000 0x07dff44990000000 0x9fffffffe0000003 0xe7fffffff8000000

def z807 : W := mkw 0x01897736c0000001 0x00625dcdb0000000 0x9381ffffe0000000 0xa4e07ffff8000000

def z808 : W := mkw 0x1dbff736c0000001 0x076ffdcdb0000000 0x8c1fffffe0000003 0x6307fffff8000000

def z809 : W := mkw 0x00000136c0000001 0x0000004db0000000 0x80001fffe0000000 0x200007fff8000000

def z810 : W := mkw 0x0022898244304a08 0x0008a260910c1282 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z811 : W := mkw 0x00a2f736c0204801 0x0028bdcdb0081200 0xe467ffffec78fc02 0xf919fffffb1e3f00

def z812 : W := mkw 0x113f8136c0000001 0x044fe04db0000000 0x801f9fffe0000000 0x6007e7fff8000000

def z813 : W := mkw 0x134900001b66d800 0x44d2400006d9b600 0x738000001ffffc00 0x1ce0000007ffff00

def z814 : W := mkw 0xa00008c9241927ac 0x28000232490649eb 0x00000000000003fc 0x00000000000000ff

def z815 : W := mkw 0x02c0268002d00058 0x80b009a000b40016 0xb3e0678003f003fc 0xacf819e000fc00ff

def z816 : W := mkw 0x0000512640000000 0x0000144990000000 0x80007fffe0000000 0x20001ffff8000000

def z817 : W := mkw 0x113f80000126d800 0x444fe0000049b600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z818 : W := mkw 0x1ffff736c2400001 0x07fffdcdb0900000 0xbfffffffe3f00003 0xeffffffff8fc0000

def z819 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xec1ff87f1c0fffe3 0xfb07fe1fc703fff8

def z820 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xdfffffffec08e003 0xf7fffffffb023800

def z821 : W := mkw 0x1f7f80241b66d800 0x47dfe00906d9b600 0x7fff807f1ffffc03 0xdfffe01fc7ffff00

def z822 : W := mkw 0x1e76dba65e74ca89 0xc79db6e9979d32a2 0x04661b870c70e000 0x011986e1c31c3800

def z823 : W := mkw 0x5fdd763c9bc79071 0x57f75d8f26f1e41c 0x1b986038138700e1 0x06e6180e04e1c038

def z824 : W := mkw 0x41892c51a58a3754 0x10624b1469628dd5 0xf7879c47ef88ff1e 0xfde1e711fbe23fc7

def z825 : W := mkw 0x0e4000001b66d800 0x4390000006d9b600 0x7b8000001ffffc01 0x1ee0000007ffff00

def z826 : W := mkw 0x1f7fd1265b66d800 0x47dff44996d9b600 0xfffffffffffffc03 0xffffffffffffff00

def z827 : W := mkw 0x02c07e801ed002d8 0x80b01fa007b400b6 0xf3e07f801ff003fc 0xbcf81fe007fc00ff

def z828 : W := mkw 0x2022898364306e0c 0x0808a260d90c1b83 0x64679f87ec78fc1e 0xd919e7e1fb1e3f07

def z829 : W := mkw 0x11bffe8005b6dad8 0xc46fffa0016db6b6 0x801fff80000ffffc 0x6007ffe00003ffff

def z830 : W := mkw 0x1ffff736c1021001 0x07fffdcdb0408400 0x9fffffffe00f1c03 0xe7fffffff803c700

def z831 : W := mkw 0x1f7f81025b66d800 0x47dfe04096d9b600 0x7fff8047fffffc03 0xdfffe011ffffff00

def z832 : W := mkw 0x1f7fd336db66d801 0x47dff4cdb6d9b600 0x7fff9bfffffffc03 0xdfffe6ffffffff00

def z833 : W := mkw 0x0c0058491c0923a0 0x03001612470248e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z834 : W := mkw 0x612b815ae12b5d24 0x184ae056b84ad749 0x00198078e00f1c00 0x4006601e3803c700

def z835 : W := mkw 0x0ed47e801ed482d8 0x83b51fa007b520b6 0xffe67f801ff0e3ff 0xbff99fe007fc38ff

def z836 : W := mkw 0x41892459a18b3574 0x106249166862cd5d 0xfb9fe47ff38fffff 0xfee7f91ffce3ffff

def z837 : W := mkw 0x0ec02c801ed00258 0x03b00b2007b40096 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z838 : W := mkw 0x13ebf736c0000001 0x04fafdcdb0000000 0x9bf9ffffe0000003 0xe6fe7ffff8000000

def z839 : W := mkw 0x1f6b80001b66d800 0x47dae00006d9b600 0x7fe180001ffffc03 0x9ff8600007ffff00

def z840 : W := mkw 0x53eba712e3e25c55 0x54fae9c4b8f89715 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z841 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xcc1ffc7ffc0fe3e3 0xf307ff1fff03f8f8

def z842 : W := mkw 0x4f495ad8bf5b17ac 0x93d256b62fd6c5eb 0x04799bf8ec7f1c00 0x411e66fe3b1fc700

def z843 : W := mkw 0x0ec07ea41ed002d8 0x83b01fa907b400b6 0xffe07fff1ff003ff 0xbff81fffc7fc00ff

def z844 : W := mkw 0x0ec07e8004900258 0x03b01fa001240096 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z845 : W := mkw 0x0d1d00001b66d800 0x4347400006d9b600 0x7f9f80001ffffc03 0xdfe7e00007ffff00

def z846 : W := mkw 0x8c145aed1c1da3a8 0xa30516bb470768ea 0xcc1e7bff1c0fe3e3 0x73079effc703f8f8

def z847 : W := mkw 0x01abf736c0000001 0x006afdcdb0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z848 : W := mkw 0xa00008c9243def2c 0x28000232490f7bcb 0x600000000c7fff1c 0x18000000031fffc7

def z849 : W := mkw 0x0f4900001b66d800 0x43d2400006d9b600 0x7ff980001ffffc03 0xdffe600007ffff00

def z850 : W := mkw 0x0ec07736c0000001 0x03b01dcdb0000000 0x9b807fffe0000001 0x26e01ffff8000000

def z851 : W := mkw 0x0dbff536c0000000 0x036ffd4db0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z852 : W := mkw 0x1ffff736db66d801 0x47fffdcdb6d9b600 0xbfffffffeff0fc03 0xeffffffffbfc3f00

def z853 : W := mkw 0x1fdd7736db469001 0x47f75dcdb6d1a400 0x9b987ffff3870001 0x26e61ffffce1c000

def z854 : W := mkw 0x1ffff736da448001 0x47fffdcdb6912000 0x9fffffffe0000003 0xe7fffffff8000000

def z855 : W := mkw 0x1f5d00001b66d800 0x47d7400006d9b600 0x7b9980001ffffc03 0xdee6600007ffff00

def z856 : W := mkw 0x7f7f88c93fffff7c 0x5fdfe2324fffffdf 0x7fff80001fffffff 0xdfffe00007ffffff

def z857 : W := mkw 0x1f7f80349b66d801 0x47dfe00d26d9b600 0x7fff80381ffffc03 0xdfffe00e07ffff00

def z858 : W := mkw 0x8ed47ea51ed4a2d8 0xa3b51fa947b528b6 0xfffe7fff1ff0e3ff 0xffff9fffc7fc38ff

def z859 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x881e787f100fe3e1 0x62079e1fc403f8f8

def z860 : W := mkw 0x02c0268002d00058 0x80b009a000b40016 0x73e0078013f003fc 0x9cf801e004fc00ff

def z861 : W := mkw 0x0ef6f72640000000 0x03bdbdc990000000 0x9fffffffe0000003 0xe7fffffff8000000

def z862 : W := mkw 0x0c14506c180d8120 0x0305141b06036048 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z863 : W := mkw 0x202281ca60394d2c 0x0808a072980e534b 0xe879e7f8f07f1fff 0xfa1e79fe3c1fc7ff

def z864 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x7b99e078f38f1ffd 0x5ee6781e3ce3c7ff

def z865 : W := mkw 0x1ffff736c0204801 0x07fffdcdb0081200 0xbfffffffe0701c03 0xeffffffff81c0700

def z866 : W := mkw 0x1ffff736db469001 0x47fffdcdb6d1a400 0xdfffffffff8fe003 0xf7ffffffffe3f800

def z867 : W := mkw 0xac1458ed3c1da7ac 0x2b05163b4f0769eb 0xcc1e787f1c0fe3ff 0x73079e1fc703f8ff

def z868 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x1fff80001ffffc01 0x47ffe00007ffff00

def z869 : W := mkw 0x600008c93ffb7ffc 0x980002324ffedfff 0x600000001ffffffc 0x1800000007ffffff

def z870 : W := mkw 0x1ef6f736da64c801 0x47bdbdcdb6993200 0x84667fffec70e000 0x21199ffffb1c3800

def z871 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xffe67fc71ff003ff 0xfff99ff1c7fc00ff

def z872 : W := mkw 0x1ffff736c1225801 0x07fffdcdb0489600 0xfffffffffffffc03 0xffffffffffffff00

def z873 : W := mkw 0x1ffff736da400001 0x07fffdcdb6900000 0x9fffffffec700003 0xe7fffffffb1c0000

def z874 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x9bf9ffffe0000001 0xa6fe7ffff8000000

def z875 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xbb99e478f3871ffd 0xaee6791e3ce1c7ff

def z876 : W := mkw 0x1ed47736c0000001 0x07b51dcdb0000000 0x80007fffe0000000 0x20001ffff8000000

def z877 : W := mkw 0x61abad9bc5b37a78 0x186aeb66f16cde9e 0x1ffe7bbf1ff7e0e1 0x07ff9eefc7fdf838

def z878 : W := mkw 0x13c97736c0000001 0x04f25dcdb0000000 0x93807fffe0000000 0x24e01ffff8000000

def z879 : W := mkw 0x113f8136c0000001 0x044fe04db0000000 0x047f9bffe0000000 0x411fe6fff8000000

def z880 : W := mkw 0x12e2f736c0000001 0x04b8bdcdb0000000 0x80607fffe0000000 0x20181ffff8000000

def z881 : W := mkw 0x8014586d1c0da3a0 0x2005161b470368e8 0xc01e787f1c0fe3e0 0x70079e1fc703f8f8

def z882 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xffe79fc7fff8ff1f 0xfff9e7f1fffe3fc7

def z883 : W := mkw 0x13eba792c3f25859 0xc4fae9e4b0fc9616 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z884 : W := mkw 0x00807736c0000001 0x00201dcdb0000000 0x9b807fffe0000003 0xa6e01ffff8000000

def z885 : W := mkw 0x1f7f800001225800 0x07dfe00000489600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z886 : W := mkw 0x136b80001b66d800 0x44dae00006d9b600 0x7bf980001ffffc03 0xdefe600007ffff00

def z887 : W := mkw 0x02c07736c0000001 0x00b01dcdb0000000 0x93e07fffe0000000 0xa4f81ffff8000000

def z888 : W := mkw 0x200008c924396f2c 0x08000232490e5bcb 0x600000001c7ffffc 0x18000000071fffff

def z889 : W := mkw 0x8014586d040da3a0 0x2005161b410368e8 0xc81e787f100fe3e3 0x72079e1fc403f8f8

def z890 : W := mkw 0x0ed47e801ed002d8 0x83b51fa007b400b6 0xfffe7f801ff003ff 0xffff9fe007fc00ff

def z891 : W := mkw 0x9e545a6d1c0da3a1 0x2795169b470368e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z892 : W := mkw 0x1febf736c0000001 0x07fafdcdb0000000 0x9fe1ffffe0000003 0xa7f87ffff8000000

def z893 : W := mkw 0xac3688c93c3defac 0x2b0da2324f0f7beb 0x6c7f80001c7fffff 0xdb1fe000071fffff

def z894 : W := mkw 0x8e545aed1e5da3a8 0xa39516bb479768ea 0xec7e7fff1c7fe3ff 0xfb1f9fffc71ff8ff

def z895 : W := mkw 0x8e54586d1c0da3a0 0x2395161b470368e8 0xdffe787f1c0fe3e3 0xf7ff9e1fc703f8f8

def z896 : W := mkw 0x119d7736c0000001 0x04675dcdb0000000 0x80187fffe0000000 0x20061ffff8000000

def z897 : W := mkw 0x1ffff736da64c801 0x47fffdcdb6993200 0xfffffffffff0e003 0xfffffffffffc3800

def z898 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xbbe07f8013f003fd 0xaef81fe004fc00ff

def z899 : W := mkw 0x600008c9259b377c 0x180002324966cddf 0x60000000138f1ffc 0x1800000004e3c7ff

def z900 : W := mkw 0x00807736c0000001 0x00201dcdb0000000 0x88187fffe0000003 0x62061ffff8000000

def z901 : W := mkw 0x8c14586d040da3a0 0x2305161b410368e8 0x8c1e787f000fe3e3 0x63079e1fc003f8f8

def z902 : W := mkw 0x1fdd76349bc690d1 0xc7f75d8d26f1a434 0x1b986038138700e1 0x06e6180e04e1c038

def z903 : W := mkw 0x1f7fd336db66d801 0x47dff4cdb6d9b600 0x047f9bffec7ffc00 0x411fe6fffb1fff00

def z904 : W := mkw 0x00a2a512c0000000 0x0028a944b0000000 0x8467ffffe0000002 0xe119fffff8000000

def z905 : W := mkw 0x73eba792e1b25c5d 0x1cfae9e4b86c9717 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z906 : W := mkw 0x1ffff736d926d801 0x47fffdcdb649b600 0xdffffffffc0ffc03 0xf7ffffffff03ff00

def z907 : W := mkw 0x8c14586d3c0da7a4 0x2305161b4f0369e9 0xcc1e7c7ffc0fe3ff 0x73079f1fff03f8ff

def z908 : W := mkw 0x1ffff736db66d801 0x47fffdcdb6d9b600 0xbffffffff3f71c03 0xeffffffffcfdc700

def z909 : W := mkw 0x600008c9253b7f2c 0x18000232494edfcb 0x600000000c7fff1c 0x18000000031fffc7

def z910 : W := mkw 0x1fdd7736c0000001 0x07f75dcdb0000000 0x9f9e7fffe0000003 0x67e79ffff8000000

def z911 : W := mkw 0x1ffff736da400081 0x87fffdcdb6900020 0x9fffffffe0000003 0xe7fffffff8000000

def z912 : W := mkw 0x0ec076001ac00050 0x03b01d8006b00014 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z913 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x7ffe00001ffffc01 0x1fff800007ffff00

def z914 : W := mkw 0x9f7fd0241b66d880 0x67dff40906d9b620 0x7fff80001ffffc03 0xdfffe00007ffff00

def z915 : W := mkw 0x8c1458ed1c1da3a8 0x2305163b470768ea 0xec1e787f1c7fe3ff 0x7b079e1fc71ff8ff

def z916 : W := mkw 0x60807fdbe49927fc 0x98201ff6f92649ff 0x80007fffe00003fc 0x20001ffff80000ff

def z917 : W := mkw 0x1ffff736c024c801 0x47fffdcdb0093200 0x9fffffffe000e003 0xe7fffffff8003800

def z918 : W := mkw 0x1ffff736dbe6d8d1 0xc7fffdcdb6f9b634 0xfffffffffffffce3 0xffffffffffffff38

def z919 : W := mkw 0x60807fffe499277d 0x18201ffff92649df 0x80007fffe00003fc 0x20001ffff80000ff

def z920 : W := mkw 0x1f7fd0001b66d800 0x47dff40006d9b600 0xfffff8001ffffc03 0xfffffe0007ffff00

def z921 : W := mkw 0x1ffff736c366d801 0x47fffdcdb0d9b600 0xbfffffffe3fffc03 0xeffffffff8ffff00

def z922 : W := mkw 0x0109000001225800 0x0042400000489600 0x7b9980001ffffc03 0xdee6600007ffff00

def z923 : W := mkw 0x1ffff736da400001 0x07fffdcdb6900000 0x9ffffffff3800003 0xe7fffffffce00000

def z924 : W := mkw 0xa00008c93f7fffac 0x680002324fdfffeb 0x600000001ffffffc 0x1800000007ffffff

def z925 : W := mkw 0xc0807efda49927fc 0xb0201fbf692649ff 0x80007fffe00003fc 0x20001ffff80000ff

def z926 : W := mkw 0x9e54586d1e4da3a0 0x6795161b479368e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z927 : W := mkw 0x0ed47e801ed482d8 0x83b51fa007b520b6 0xfff87f801ff703ff 0xbffe1fe007fdc0ff

def z928 : W := mkw 0x012b80001b66d800 0x404ae00006d9b600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z929 : W := mkw 0xa00008c924396fac 0x28000232490e5beb 0x600000000c78fffc 0x18000000031e3fff

def z930 : W := mkw 0x1f7fd3265b66d801 0x47dff4c996d9b600 0xffff9fc7fffffc03 0xffffe7f1ffffff00

def z931 : W := mkw 0x0c1458241c048280 0x03051609070120a0 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z932 : W := mkw 0x1ffff736d9069001 0x07fffdcdb641a400 0xffffffffff8ffc03 0xffffffffffe3ff00

def z933 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xcc7e7fff1c0fe3e3 0xf31f9fffc703f8f8

def z934 : W := mkw 0x0ec07e801ed482d8 0x83b01fa007b520b6 0xffe07f801fffe3ff 0xbff81fe007fff8ff

def z935 : W := mkw 0x0ec02e801ed002d8 0x83b00ba007b400b6 0x7fe007801ff003ff 0x9ff801e007fc00ff

def z936 : W := mkw 0x1ffff736c1821051 0x07fffdcdb0608414 0xfffffffff38f1fff 0xfffffffffce3c7ff

def z937 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0xffff9f801ffffc03 0xffffe7e007ffff00

def z938 : W := mkw 0x8014506d000da1a0 0x2005141b40036868 0x001e607f000fe0e0 0x4007981fc003f838

def z939 : W := mkw 0x1ef6f736c0000001 0x07bdbdcdb0000000 0x8c7e7fffe0000003 0x631f9ffff8000000

def z940 : W := mkw 0x1f7f81265b66d801 0x47dfe04996d9b600 0x7fff80071ffffc03 0xdfffe001c7ffff00

def z941 : W := mkw 0x612b88c925bb7f7c 0x184ae232496edfdf 0x7fff80001fffffff 0xdfffe00007ffffff

def z942 : W := mkw 0x1ffff736c0204801 0x07fffdcdb0081200 0x9fffffffec70e003 0xe7fffffffb1c3800

def z943 : W := mkw 0x137f80000366d800 0x44dfe00000d9b600 0x77ff80000ffffc02 0xddffe00003ffff00

def z944 : W := mkw 0x1ffff736c2c00051 0x87fffdcdb0b00014 0x9fffffffe3800003 0xe7fffffff8e00000

def z945 : W := mkw 0x8e54586d1e4da3a0 0x2395161b479368e8 0xcc7e787f1c7fe3e3 0x731f9e1fc71ff8f8

def z946 : W := mkw 0x11bfa536c0000001 0x046fe94db0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z947 : W := mkw 0x73eba592e3f25c5c 0x5cfae964b8fc9717 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z948 : W := mkw 0x0c1408491c0da320 0x03050212470368c8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z949 : W := mkw 0x1ffff736d8048001 0x07fffdcdb6012000 0x9ffffffff0070003 0xe7fffffffc01c000

def z950 : W := mkw 0x0c807c801c9002d8 0x03201f20072400b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z951 : W := mkw 0x1f7fd3265b66d801 0x47dff4c996d9b600 0xfffffbff1ffffc03 0xfffffeffc7ffff00

def z952 : W := mkw 0x0c14586d04092320 0x0305161b410248c8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z953 : W := mkw 0x202289cb64396f2c 0x0808a272d90e5bcb 0xe467ffffec78fffe 0xf919fffffb1e3fff

def z954 : W := mkw 0x02c07e8006d002d8 0x80b01fa001b400b6 0xfbe07f8013f003ff 0xbef81fe004fc00ff

def z955 : W := mkw 0x8014006d000da120 0x2005001b40036848 0x801e607f000fe3e0 0x6007981fc003f8f8

def z956 : W := mkw 0x024000001b66d800 0x4090000006d9b600 0x73e000001ffffc00 0x9cf8000007ffff00

def z957 : W := mkw 0x1f7f8112db66d801 0x47dfe044b6d9b600 0x7fff8000fffffc03 0xdfffe0003fffff00

def z958 : W := mkw 0x113fd336c0000001 0x044ff4cdb0000000 0x001f9bffe0000000 0x4007e6fff8000000

def z959 : W := mkw 0x1fffa512db66d800 0x47ffe944b6d9b600 0xfffffffffffffc03 0xffffffffffffff00

def z960 : W := mkw 0x0ed47ea41ed002d8 0x83b51fa907b400b6 0xffe67f871ff003ff 0xbff99fe1c7fc00ff

def z961 : W := mkw 0x8c14502d1805a0a0 0x2305140b46016828 0x081e603f1007e0e1 0x0207980fc401f838

def z962 : W := mkw 0x1f5d00001b66d800 0x47d7400006d9b600 0x7f9e00001ffffc03 0x5fe7800007ffff00

def z963 : W := mkw 0x8c14506d000da120 0x2305141b40036848 0xcc1e787f100fe3e3 0x73079e1fc403f8f8

def z964 : W := mkw 0x1f5d00001b66d800 0x47d7400006d9b600 0x7ff800001ffffc03 0x9ffe000007ffff00

def z965 : W := mkw 0x1ed47e801ed482d8 0xc7b51fa007b520b6 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z966 : W := mkw 0x600008c924b96f7c 0x18000232492e5bdf 0x600000000c78fffc 0x18000000031e3fff

def z967 : W := mkw 0x1f7fd336c0000001 0x07dff4cdb0000000 0x8c7ffbffe0000003 0x631ffefff8000000

def z968 : W := mkw 0x0c947736d8048001 0x03251dcdb6012000 0xcc1e7ffffc0fe003 0x73079fffff03f800

def z969 : W := mkw 0x1ffff736c0204801 0x07fffdcdb0081200 0x9fffffffe008fc03 0xe7fffffff8023f00

def z970 : W := mkw 0x1ffff736c0800051 0x07fffdcdb0200014 0xbfffffffe380001f 0xeffffffff8e00007

def z971 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xfff87f801fff03ff 0xfffe1fe007ffc0ff

def z972 : W := mkw 0x1ffff736db66d801 0x47fffdcdb6d9b600 0x9ffffffffff7e003 0xe7fffffffffdf800

def z973 : W := mkw 0x1f7fd0241b66d800 0x47dff40906d9b600 0x7fff98071ffffc03 0xdfffe601c7ffff00

def z974 : W := mkw 0x8c1458ed3c1da7ac 0x2305163b4f0769eb 0xec7ffffffc7fffff 0xfb1fffffff1fffff

def z975 : W := mkw 0x13eba712c0000001 0x04fae9c4b0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z976 : W := mkw 0x0022814260284d04 0x0008a050980a1341 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z977 : W := mkw 0x00802512c0000000 0x00200944b0000000 0x80007fffe0000000 0x20001ffff8000000

def z978 : W := mkw 0x8c14586d3c0da7a4 0x2305161b4f0369e9 0xec1e787f1c0fffff 0x7b079e1fc703ffff

def z979 : W := mkw 0x8c14506d180da1a0 0x2305141b46036868 0x4c1e607f1c0fe0e3 0x5307981fc703f838

def z980 : W := mkw 0x0ee2f736c0000001 0x03b8bdcdb0000000 0x9fe7ffffe0000003 0xe7f9fffff8000000

def z981 : W := mkw 0x0febf712c0000000 0x03fafdc4b0000000 0x9fffffffe0000003 0xe7fffffff8000000

def z982 : W := mkw 0x1ffff736da64c801 0x47fffdcdb6993200 0xffffffffec78fc03 0xfffffffffb1e3f00

def z983 : W := mkw 0x1f7f8136c0000001 0x07dfe04db0000000 0x9fff9fffe0000003 0xe7ffe7fff8000000

def z984 : W := mkw 0x8e545aed1e5da3a8 0xa39516bb479768ea 0xfffe7bff1fffe3e3 0xffff9effc7fff8f8

def z985 : W := mkw 0x136b80001b66d800 0x44dae00006d9b600 0x77e780001ffffc02 0xddf9e00007ffff00

def z986 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xffffffffec700003 0xfffffffffb1c0000

def z987 : W := mkw 0x2022898364306e0c 0x0808a260d90c1b83 0xe4679f87ec70ff1e 0xb919e7e1fb1c3fc7

def z988 : W := mkw 0x1ffff736d8048001 0x07fffdcdb6012000 0x9fffffffec00e003 0xe7fffffffb003800

def z989 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x77e01f801ff003fc 0x9df807e007fc00ff

def z990 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xffffffffe000031f 0xfffffffff80000c7

def z991 : W := mkw 0x2022898364306e0c 0x0808a260d90c1b83 0xa4679fc7ec70fc1e 0xe919e7f1fb1c3f07

def z992 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x841e787f0c0fe3e0 0x61079e1fc303f8f8

def z993 : W := mkw 0x1ffff736c1021001 0x07fffdcdb0408400 0xbfffffffe3801c03 0xeffffffff8e00700

def z994 : W := mkw 0x13fff736c0000001 0x04fffdcdb0000000 0x93ffffffe0000000 0xe4fffffff8000000

def z995 : W := mkw 0x1f7fd0241b66d800 0x47dff40906d9b600 0x7fffe0381ffffc03 0xdffff80e07ffff00

def z996 : W := mkw 0x02c02e8006d002d8 0x80b00ba001b400b6 0x33e0078003f003fc 0x8cf801e000fc00ff

def z997 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0x77e780001ffffc00 0x9df9e00007ffff00

def z998 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x64679f87ec78ff1c 0x9919e7e1fb1e3fc7

def z999 : W := mkw 0xc00008c93fdfb7fc 0xb00002324ff7edff 0x600000001ffffffc 0x1800000007ffffff

def z1000 : W := mkw 0x8e54586d1e4da3a0 0x2395161b479368e8 0xdf9e787f1f8fe3e3 0x77e79e1fc7e3f8f8

def z1001 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0x24679fc7ec78fc1c 0xc919e7f1fb1e3f07

def z1002 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xec7fffffec78ff1f 0xfb1ffffffb1e3fc7

def z1003 : W := mkw 0x010900001b66d800 0x4042400006d9b600 0x7b9800001ffffc01 0x1ee6000007ffff00

def z1004 : W := mkw 0x8c14006d180da120 0x2305001b46036848 0xcc1e607f1c0fe3e3 0x7307981fc703f8f8

def z1005 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x4c1e783f1c0fe3e1 0x13079e0fc703f8f8

def z1006 : W := mkw 0x13ebf736c3625801 0x44fafdcdb0d89600 0xb3e1ffffe3f01c00 0xacf87ffff8fc0700

def z1007 : W := mkw 0x0ec076801ad000d8 0x83b01da006b40036 0xfbe0678013f003ff 0xbef819e004fc00ff

def z1008 : W := mkw 0x1ffff736da64c801 0x47fffdcdb6993200 0xdffffffffc7fe003 0xf7ffffffff1ff800

def z1009 : W := mkw 0x00228136c0000001 0x0008a04db0000000 0x84679fffe0000002 0xe119e7fff8000000

def z1010 : W := mkw 0x0e5400001b66d800 0x4395000006d9b600 0x7ffe00001ffffc03 0xdfff800007ffff00

def z1011 : W := mkw 0x1ffff736db66d801 0x47fffdcdb6d9b600 0x9ffffffff38ffc03 0xe7fffffffce3ff00

def z1012 : W := mkw 0x0022d12640000000 0x0008b44990000000 0x8467ffffe0000002 0xe119fffff8000000

def z1013 : W := mkw 0x1f7f81025b66d800 0x47dfe04096d9b600 0x7fff9b871ffffc03 0xdfffe6e1c7ffff00

def z1014 : W := mkw 0x8014086d1c0da3a0 0x2005021b470368e8 0xc81e607f1c0fe3e3 0x7207981fc703f8f8

def z1015 : W := mkw 0x00a2f736c0000001 0x0028bdcdb0000000 0x8007ffffe0000000 0x6001fffff8000000

def z1016 : W := mkw 0x1f7f81025b66d800 0x47dfe04096d9b600 0x7fff8780fffffc03 0xdfffe1e03fffff00

def z1017 : W := mkw 0x8ec07e811ed4a2d8 0xa3b01fa047b528b6 0xffe07f801ff0e3ff 0xbff81fe007fc38ff

def z1018 : W := mkw 0x9ffff736d8048081 0x27fffdcdb6012020 0x9fffffffe0000003 0xe7fffffff8000000

def z1019 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x1ffffbffe0000001 0x47fffefff8000000

def z1020 : W := mkw 0x0f6b80001b625800 0x03dae00006d89600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z1021 : W := mkw 0x8014586d040da3a0 0x2005161b410368e8 0xc41e787f0c0fe3e2 0x71079e1fc303f8f8

def z1022 : W := mkw 0x202289c364386f0c 0x0808a270d90e1bc3 0xec67ffc7fc78ffff 0xfb19fff1ff1e3fff

def z1023 : W := mkw 0x11bff736c0000001 0x046ffdcdb0000000 0x9b9fffffe0000003 0xe6e7fffff8000000

def z1024 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x97e7ffffe0000000 0xa5f9fffff8000000

def z1025 : W := mkw 0x8ec07ea51ed022d8 0xa3b01fa947b408b6 0xffe07f871ff003ff 0xbff81fe1c7fc00ff

def z1026 : W := mkw 0x0ec0768002d00058 0x83b01da000b40016 0xffe07f8013f003ff 0xbff81fe004fc00ff

def z1027 : W := mkw 0x01897736c0000001 0x00625dcdb0000000 0x9b987fffe0000001 0x26e61ffff8000000

def z1028 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xffffffffe0081c03 0xfffffffff8020700

def z1029 : W := mkw 0x1ffff736db469001 0x47fffdcdb6d1a400 0xfffffffffff70003 0xfffffffffffdc000

def z1030 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x7be067801ff003fd 0x9ef819e007fc00ff

def z1031 : W := mkw 0x0c947736c0000001 0x03251dcdb0000000 0x84067fffe0000000 0x21019ffff8000000

def z1032 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0xec1e7c7f1c0fe3ff 0xfb079f1fc703f8ff

def z1033 : W := mkw 0x0f5d00001b469000 0x03d7400006d1a400 0x7fff80001ffffc03 0xdfffe00007ffff00

def z1034 : W := mkw 0x1ffff736c3421001 0x47fffdcdb0d08400 0x9fffffffe3800003 0xe7fffffff8e00000

def z1035 : W := mkw 0x137f80001b66d800 0x44dfe00006d9b600 0x73ff80001ffffc00 0xdcffe00007ffff00

def z1036 : W := mkw 0x1ffff736da448001 0x07fffdcdb6912000 0xffffffffffffe003 0xfffffffffffff800

def z1037 : W := mkw 0x0c36d1265824c800 0x030db44996093200 0xec7ffffffc7ffc03 0xfb1fffffff1fff00

def z1038 : W := mkw 0x800008491c0da3a0 0x20000212470368e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z1039 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0xfffffffff3800003 0xfffffffffce00000

def z1040 : W := mkw 0x713f815be12ffd24 0x5c4fe056f84bff49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z1041 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xfff9fff8f38f1fff 0xfffe7ffe3ce3c7ff

def z1042 : W := mkw 0x00807736c08000d1 0x80201dcdb0200034 0x80007fffe00000e0 0x20001ffff8000038

def z1043 : W := mkw 0x8c14582d1c05a2a0 0x2305160b470168a8 0x4c1e783f1c0fe0e3 0x53079e0fc703f838

def z1044 : W := mkw 0xbf7f88c93f7fffac 0x6fdfe2324fdfffeb 0x7fff80001fffffff 0xdfffe00007ffffff

def z1045 : W := mkw 0xa00008c93c1da7ac 0x280002324f0769eb 0x400000001c0fe3fc 0x100000000703f8ff

def z1046 : W := mkw 0x1fdd7736c0000001 0x07f75dcdb0000000 0x9ff87fffe0000003 0xa7fe1ffff8000000

def z1047 : W := mkw 0xe00008c93dbffffc 0x380002324f6fffff 0x600000001ffffffc 0x1800000007ffffff

def z1048 : W := mkw 0x00a2f736c0000001 0x0028bdcdb0000000 0x8061ffffe0000000 0xa0187ffff8000000

def z1049 : W := mkw 0x1ffff736db625801 0x47fffdcdb6d89600 0xfffffffffff01c03 0xfffffffffffc0700

def z1050 : W := mkw 0x13ebf736c0000001 0x04fafdcdb0000000 0x97e7ffffe0000002 0xe5f9fffff8000000

def z1051 : W := mkw 0x8c1458ed1c1da3a8 0x2305163b470768ea 0xcc1e7fff1c0fe3ff 0x73079fffc703f8ff

def z1052 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xb7e07f800ff003fc 0xadf81fe003fc00ff

def z1053 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x7b99e438f38f1ffd 0x9ee6790e3ce3c7ff

def z1054 : W := mkw 0x1ffff736c1069001 0x47fffdcdb041a400 0x9fffffffe0070003 0xe7fffffff801c000

def z1055 : W := mkw 0x00807736c0800051 0x00201dcdb0200014 0xfb807ffff38003ff 0xbee01ffffce000ff

def z1056 : W := mkw 0x1ffff736da604801 0x07fffdcdb6981200 0xfffffffffff8fc03 0xfffffffffffe3f00

def z1057 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0xffffe0001fffffe3 0xfffff80007fffff8

def z1058 : W := mkw 0x202289cb64396f2c 0x0808a272d90e5bcb 0xe47f9fffec7fff1e 0xf91fe7fffb1fffc7

def z1059 : W := mkw 0x8c14586d1c0da3a0 0x2305161b470368e8 0x8c1e787f1c07e3e1 0x23079e1fc701f8f8

def z1060 : W := mkw 0x1ffff736c0048001 0x07fffdcdb0012000 0x9fffffffe00fe003 0xe7fffffff803f800

def z1061 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0xfff87ff81ff003ff 0xfffe1ffe07fc00ff

def z1062 : W := mkw 0x8c1458ed1e5da3a8 0xa305163b479768ea 0xcc1e787f1c7fe3e3 0x73079e1fc71ff8f8

def z1063 : W := mkw 0xb13f816f612ffd24 0x6c4fe05bd84bff49 0x001f807fe00ffc00 0x4007e01ff803ff00

def z1064 : W := mkw 0x13ffa736c0000001 0x04ffe9cdb0000000 0x97ff9fffe0000002 0xe5ffe7fff8000000

def z1065 : W := mkw 0x8c14582d1c05a2a0 0x2305160b470168a8 0xcc1e783f1c07e3e3 0x33079e0fc701f8f8

def z1066 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x9ffe7fffe0000001 0x27ff9ffff8000000

def z1067 : W := mkw 0x10b6f736c0000001 0x042dbdcdb0000000 0x80067fffe0000000 0x20019ffff8000000

def z1068 : W := mkw 0x00807736c0000001 0x00201dcdb0000000 0x8001ffffe0000002 0xe0007ffff8000000

def z1069 : W := mkw 0x11bff736c0000001 0x046ffdcdb0000000 0x847fffffe0000002 0xe11ffffff8000000

def z1070 : W := mkw 0x1f7fd336c0000001 0x07dff4cdb0000000 0x1fff9bffe0000003 0xc7ffe6fff8000000

def z1071 : W := mkw 0x113f80001b66d800 0x444fe00006d9b600 0x7b9f80001ffffc03 0xdee7e00007ffff00

def z1072 : W := mkw 0x1f7fd0001b66d880 0x47dff40006d9b620 0x7fffe0001ffffce3 0xdffff80007ffff38

def z1073 : W := mkw 0x1ffff736c3625801 0x47fffdcdb0d89600 0xffffffffeff8fc03 0xfffffffffbfe3f00

def z1074 : W := mkw 0x8c14506d180da1a0 0x2305141b46036868 0x8c1e787f100fe0e3 0x63079e1fc403f838

def z1075 : W := mkw 0x1ffff736db66d801 0x47fffdcdb6d9b600 0x9fffffffec7ffc03 0xe7fffffffb1fff00

def z1076 : W := mkw 0x1ffff736c1225801 0x47fffdcdb0489600 0x9fffffffe0001c03 0xe7fffffff8000700

def z1077 : W := mkw 0x01aba512c1225800 0x006ae944b0489600 0xfffffffffffffc03 0xffffffffffffff00

def z1078 : W := mkw 0x1ffff736dac00051 0x07fffdcdb6b00014 0xfffffffffff003ff 0xfffffffffffc00ff

def z1079 : W := mkw 0x1ffff736db469001 0x47fffdcdb6d1a400 0xfffffffff38f1c03 0xfffffffffce3c700

def z1080 : W := mkw 0x8c14586d3c0da7a4 0x2305161b4f0369e9 0xcc1ff87ffc0fffe3 0x7307fe1fff03fff8

def z1081 : W := mkw 0x202289cb64396f2c 0x0808a272d90e5bcb 0xe4679fc7fc7ffffe 0xf919e7f1ff1fffff

def z1082 : W := mkw 0x1ffff736d824c801 0x07fffdcdb6093200 0xfffffffffc7ffc03 0xffffffffff1fff00

def z1083 : W := mkw 0x00807736c0800051 0x00201dcdb0200014 0x80007fffe00003fc 0x20001ffff80000ff

def z1084 : W := mkw 0x0036812640000000 0x000da04990000000 0x847f9fffe0000002 0xe11fe7fff8000000

def z1085 : W := mkw 0x0e7680001a64c800 0x039da00006993200 0x7fff80001ffffc03 0xdfffe00007ffff00

def z1086 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x847fffffe0000000 0x611ffffff8000000

def z1087 : W := mkw 0x8e545a6d1e4da3a0 0xa395169b479368e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z1088 : W := mkw 0x60802cd9a499277c 0x18200b36692649df 0x80006478e00003fc 0x2000191e380000ff

def z1089 : W := mkw 0x0000004900092120 0x0000001240024848 0xc81e607f100fe3e3 0x7207981fc403f8f8

def z1090 : W := mkw 0xa00008c93efdeffc 0xa80002324fbf7bff 0x600000001ffffffc 0x1800000007ffffff

def z1091 : W := mkw 0x8c14506d180da1a0 0x2305141b46036868 0xc81e607f100fe3e3 0x7207981fc403f8f8

def z1092 : W := mkw 0x8c1458ed1c1da3a8 0x2305163b470768ea 0xcc7e7bff1c7fe3e3 0x731f9effc71ff8f8

def z1093 : W := mkw 0x01897736c1021001 0x00625dcdb0408400 0xfb99fffff38f1c03 0xfee67ffffce3c700

def z1094 : W := mkw 0x0080248000900058 0x0020092000240016 0xfbe0678013f003ff 0xbef819e004fc00ff

def z1095 : W := mkw 0x012b8112c0000000 0x004ae044b0000000 0x847f9fffe0000002 0xe11fe7fff8000000

def z1096 : W := mkw 0x8c14582d1c05a2a0 0x2305160b470168a8 0x8c1e787f1c07e0e3 0x63079e1fc701f838

def z1097 : W := mkw 0x1ffff736c0800051 0x07fffdcdb0200014 0x9fffffffe00003ff 0xe7fffffff80000ff

def z1098 : W := mkw 0x0ec07736dac000d1 0x83b01dcdb6b00034 0x9b807ffff38000e1 0x26e01ffffce00038

def z1099 : W := mkw 0x8ed47ea51ed4a2d8 0xa3b51fa947b528b6 0xfffe7f871fffe3ff 0xffff9fe1c7fff8ff

def z1100 : W := mkw 0x1f7fd2241b66d801 0x47dff48906d9b600 0x7fff80001ffffc03 0xdfffe00007ffff00

def z1101 : W := mkw 0x63eba792e3f25c5c 0x98fae9e4b8fc9717 0x33e18780e3f01c1c 0x8cf861e038fc0707

def z1102 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0xff9fe478ff8fffff 0xffe7f91e3fe3ffff

def z1103 : W := mkw 0x8014006d000da120 0x2005001b40036848 0x081e607f100fe0e1 0x4207981fc403f838

def z1104 : W := mkw 0x1fdd7736c0000001 0x07f75dcdb0000000 0x9b99ffffe0000003 0xe6e67ffff8000000

def z1105 : W := mkw 0x01892512c0000000 0x00624944b0000000 0x9b99ffffe0000003 0xe6e67ffff8000000

def z1106 : W := mkw 0x41892458a18b1574 0x106249162862c55d 0x9b99e478f38f1ffd 0x66e6791e3ce3c7ff

def z1107 : W := mkw 0x1ffff736dac000d1 0x87fffdcdb6b00034 0xfffffffffff000e3 0xfffffffffffc0038

def z1108 : W := mkw 0x0cb6f736c0000001 0x032dbdcdb0000000 0x8c7fffffe0000003 0xe31ffffff8000000

def z1109 : W := mkw 0x0ec07e801ed002d8 0x83b01fa007b400b6 0x7fe07b801ff003fd 0x1ff81ee007fc00ff

def z1110 : W := mkw 0x1ffff736dac000d1 0x87fffdcdb6b00034 0xfffffffff38003ff 0xfffffffffce000ff

def z1111 : W := mkw 0x5ffff736c1821051 0x17fffdcdb0608414 0x9fffffffe3800003 0xe7fffffff8e00000

def z1112 : W := mkw 0x1ef6f736c0000001 0x07bdbdcdb0000000 0x9fe67fffe0000003 0xa7f99ffff8000000

def z1113 : W := mkw 0x02c07e8006d002d8 0x80b01fa001b400b6 0xf7e07f800ff003fe 0xbdf81fe003fc00ff

def z1114 : W := mkw 0x1ffff736d8000081 0x07fffdcdb6000020 0x9ffffffff00000e3 0xe7fffffffc000038

def z1115 : W := mkw 0x01090048210b1524 0x004240120842c549 0xfb99e478f38f1fff 0xfee6791e3ce3c7ff

def z1116 : W := mkw 0xbe76d9a75e74ea88 0x6f9db669d79d3aa2 0x04661b870c70e000 0x011986e1c31c3800

def z1117 : W := mkw 0x8e545a6d1c0da3a0 0x2395169b470368e8 0xcc7e7bff1c0fe3e3 0x731f9effc703f8f8

def z1118 : W := mkw 0x02c02e801ed002d8 0x80b00ba007b400b6 0xf7e01f801ff003fe 0xbdf807e007fc00ff

def z1119 : W := mkw 0x1ffff736c0000001 0x07fffdcdb0000000 0x9b9fffffe0000001 0x66e7fffff8000000

def z1120 : W := mkw 0x8000586d040923a0 0x2000161b410248e8 0xcc1e787f1c0fe3e3 0x73079e1fc703f8f8

def z1121 : W := mkw 0x00a2f736c0000001 0x0028bdcdb0000000 0x84667fffe0000000 0x21199ffff8000000

def z1122 : W := mkw 0x01897736c0000001 0x00625dcdb0000000 0x8019ffffe0000000 0x60067ffff8000000

def z1123 : W := mkw 0x0ed47736c0000001 0x03b51dcdb0000000 0x9ffe7fffe0000003 0xe7ff9ffff8000000

def z1124 : W := mkw 0xe0807dffe49927fc 0x38201f7ff92649ff 0x80007fffe00003fc 0x20001ffff80000ff

def z1125 : W := mkw 0x000008c12418270c 0x00000230490609c3 0xe4679fc7ec78ff1e 0xf919e7f1fb1e3fc7

def z1126 : W := mkw 0x1ffff736c3625801 0x47fffdcdb0d89600 0xfffffffff3ff1c03 0xfffffffffcffc700

def z1127 : W := mkw 0x1f7fd2001b66d880 0xc7dff48006d9b620 0x7fff80001ffffc03 0xdfffe00007ffff00

def z1128 : W := mkw 0x1ffff736c1021001 0x07fffdcdb0408400 0x9ffffffff3870003 0xe7fffffffce1c000

def z1129 : W := mkw 0x1ffff736c08000d1 0x87fffdcdb0200034 0x9fffffffe00000e3 0xe7fffffff8000038

def z1130 : W := mkw 0x1f7fd336c0000001 0x07dff4cdb0000000 0x847f9fffe0000002 0xe11fe7fff8000000

def z1131 : W := mkw 0x0c807736c0000001 0x03201dcdb0000000 0x8c007fffe0000003 0x23001ffff8000000

def z1132 : W := mkw 0x1ef6f736c0000001 0x07bdbdcdb0000000 0x8467ffffe0000002 0xe119fffff8000000

def z1133 : W := mkw 0x0ec07736da400001 0x03b01dcdb6900000 0xffe07ffffff00003 0xbff81ffffffc0000

def z1134 : W := mkw 0x0ec07736c0000001 0x03b01dcdb0000000 0x84607fffe0000000 0x21181ffff8000000

def z1135 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0xffff98471ffffc03 0xffffe611c7ffff00

def z1136 : W := mkw 0x00807736c0000001 0x00201dcdb0000000 0x84067fffe0000002 0x61019ffff8000000

def z1137 : W := mkw 0x0e4058801e500288 0x03901620079400a2 0xffe07f801ff003ff 0xbff81fe007fc00ff

def z1138 : W := mkw 0x1f7f80001b66d800 0x47dfe00006d9b600 0xffff8440fffffc03 0xffffe1103fffff00

def z1139 : W := mkw 0x0e6280001b66d800 0x4398a00006d9b600 0x7fe780001ffffc03 0xdff9e00007ffff00

def z1140 : W := mkw 0x0ec026801ad00058 0x83b009a006b40016 0xffe067801ff003ff 0xbff819e007fc00ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z9,z4,z5,z6]),(0,[z10,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z3,z4,z12,z5,z6]),(0,[z0,z2,z3,z13,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z14]),(0,[z0,z2,z3,z4,z5,z6,z15])],[(0,[z0,z2,z16,z17,z4,z5,z6]),(0,[z0,z2,z16,z4,z18,z5,z6]),(0,[z0,z2,z3,z4,z19,z5,z6])],[(0,[z20,z2,z3,z17,z4,z5,z6]),(0,[z21,z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z23,z4,z5,z6]),(1,[z2,z3,z4,z5,z24,z6])],[(0,[z25,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z26]),(0,[z0,z27,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z28,z4,z5,z6]),(1,[z29,z2,z3,z4,z30,z6]),(0,[z2,z3,z4,z31,z5,z6,z32]),(0,[z0,z2,z3,z4,z5,z33,z6]),(0,[z0,z2,z34,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z35,z6]),(0,[z0,z36,z2,z3,z4,z5,z6])],[(0,[z0,z37,z2,z3,z4,z5,z6]),(0,[z0,z1,z38,z2,z4,z5,z6]),(0,[z0,z39,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z4,z5,z6,z41]),(0,[z0,z2,z4,z5,z6,z42,z43])],[(0,[z0,z2,z3,z4,z5,z6,z44]),(0,[z45,z0,z2,z4,z18,z5,z6])],[(0,[z46,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z6,z47]),(0,[z0,z48,z2,z3,z4,z5,z6]),(0,[z49,z0,z50,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z51])]],
   [[(0,[z52,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z53,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z54,z6]),(0,[z55,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z56,z3,z4,z5,z6]),(0,[z0,z57,z2,z3,z4,z5,z6])],[(0,[z58,z0,z20,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z59,z6]),(0,[z60,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z16,z4,z5,z6]),(0,[z0,z3,z62,z4,z63,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z6])],[(0,[z65,z66,z0,z3,z4,z5,z6]),(1,[z0,z67,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z68]),(0,[z69,z0,z2,z3,z4,z5,z6]),(0,[z0,z38,z2,z4,z18,z5,z6])],[(0,[z49,z66,z0,z2,z4,z5,z6]),(0,[z70,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z71,z4,z5,z6]),(0,[z0,z72,z2,z3,z4,z5,z6]),(0,[z49,z0,z2,z4,z73,z5,z6])],[(0,[z58,z0,z2,z16,z4,z5,z6]),(0,[z0,z74,z3,z16,z4,z5,z6]),(0,[z65,z0,z3,z4,z5,z6,z75]),(0,[z0,z74,z2,z3,z63,z5,z6]),(0,[z76,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z77])],[(1,[z0,z2,z3,z4,z5,z78]),(0,[z79,z0,z2,z3,z80,z5,z6]),(0,[z0,z81,z2,z3,z4,z5,z6]),(0,[z82,z0,z2,z3,z4,z5,z6]),(0,[z83,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z84,z6])],[(0,[z0,z2,z85,z3,z4,z5,z6])],[(0,[z49,z0,z2,z4,z5,z6,z86])]],
   [[(0,[z0,z87,z3,z16,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z88,z6]),(0,[z49,z0,z2,z89,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z6]),(0,[z0,z2,z3,z4,z91,z5,z6]),(1,[z0,z2,z3,z92,z5,z6])],[(0,[z8,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z93,z5,z6]),(0,[z94,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z5,z6]),(0,[z0,z2,z96,z97,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z98,z6]),(0,[z0,z2,z3,z23,z4,z99,z6]),(1,[z100,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z101,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z102,z6]),(0,[z103,z0,z2,z3,z4,z5,z104])],[(0,[z105,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z106,z6]),(1,[z0,z16,z4,z63,z5,z6]),(0,[z65,z0,z3,z4,z63,z5,z6]),(0,[z0,z2,z107,z3,z4,z5,z6]),(0,[z0,z2,z3,z108,z4,z5,z6]),(0,[z109,z0,z2,z3,z4,z18,z6])],[(0,[z110,z0,z2,z111,z4,z5,z6]),(0,[z0,z112,z2,z3,z4,z5,z6]),(0,[z0,z2,z96,z16,z4,z5,z6]),(0,[z113,z0,z2,z3,z4,z5,z6]),(0,[z114,z0,z2,z3,z4,z5,z6]),(0,[z115,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z97,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z5,z6])],[(0,[z117,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z118,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z32]),(0,[z119,z49,z0,z2,z4,z5,z6]),(0,[z45,z0,z2,z4,z5,z88,z6])],[(0,[z120,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z89,z4,z5,z43])],[(0,[z110,z0,z2,z3,z80,z5,z6]),(0,[z29,z121,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z122]),(0,[z0,z2,z3,z123,z4,z5,z6]),(0,[z0,z2,z3,z16,z4,z5,z6]),(0,[z0,z2,z3,z89,z5,z104,z6])]],
   [[(0,[z0,z2,z67,z3,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z124,z6]),(0,[z0,z2,z3,z125,z4,z5,z6]),(0,[z126,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z127,z6])],[],[(0,[z66,z58,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z128,z5,z6]),(0,[z0,z2,z3,z4,z129,z5,z6]),(0,[z0,z130,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z23,z4,z104,z6]),(0,[z0,z2,z3,z4,z131,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z32]),(0,[z109,z0,z2,z97,z4,z5,z6]),(0,[z94,z0,z2,z3,z89,z4,z5])],[(0,[z0,z2,z132,z3,z4,z5,z6]),(0,[z110,z2,z3,z80,z4,z5,z6]),(1,[z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z134,z6]),(0,[z0,z135,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z136,z5,z32]),(0,[z49,z0,z2,z4,z5,z88,z6]),(0,[z40,z0,z61,z2,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z137]),(0,[z0,z2,z3,z4,z138,z5,z6])],[(0,[z0,z2,z139,z3,z4,z5,z6]),(0,[z109,z0,z2,z16,z4,z5,z6])],[]],
   [[(0,[z66,z0,z20,z3,z4,z5,z6]),(0,[z140,z0,z2,z3,z4,z5,z6]),(0,[z141,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z142,z4,z5,z6]),(0,[z45,z40,z0,z2,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z88]),(0,[z143,z0,z2,z3,z4,z5,z6])],[(1,[z40,z0,z2,z4,z5,z41])],[(0,[z144,z0,z2,z3,z4,z5,z6]),(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z146,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z147,z6]),(0,[z66,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z148,z5,z6]),(0,[z149,z0,z2,z3,z4,z5,z6]),(0,[z0,z150,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z151]),(0,[z152,z0,z2,z3,z4,z5,z6])],[(0,[z153,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z154]),(0,[z29,z0,z2,z3,z4,z31,z6]),(0,[z0,z2,z16,z4,z5,z30,z6]),(0,[z155,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z104,z6]),(0,[z0,z2,z3,z4,z5,z156,z6]),(0,[z0,z2,z157,z3,z4,z5,z6])],[(0,[z0,z2,z3,z158,z4,z5,z6]),(0,[z159,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z160,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z161]),(0,[z0,z162,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z163,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z164]),(1,[z165,z0,z3,z4,z5,z6])],[(0,[z0,z166,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z167,z6]),(0,[z11,z0,z3,z4,z63,z5,z6]),(0,[z0,z168,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z169,z5,z6])],[(0,[z0,z2,z3,z4,z170,z5,z6]),(0,[z0,z2,z3,z171,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z172])]],
   [[(0,[z0,z2,z3,z4,z173,z5,z6]),(0,[z49,z40,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z6])],[(0,[z0,z2,z3,z4,z5,z175,z6]),(0,[z176,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z177,z4,z5,z6]),(0,[z0,z2,z178,z3,z4,z5,z6]),(0,[z0,z2,z3,z179,z4,z5,z6])],[(0,[z0,z2,z16,z9,z4,z5,z6]),(0,[z180,z0,z2,z3,z4,z5,z6]),(0,[z0,z181,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z136,z182])],[(0,[z121,z2,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z12,z5,z6]),(0,[z0,z183,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z184]),(0,[z0,z2,z3,z4,z5,z6,z185])],[(1,[z0,z2,z3,z4,z5,z186]),(0,[z187,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z188,z5,z6]),(1,[z115,z0,z3,z4,z5,z75]),(0,[z0,z2,z3,z4,z5,z6,z189])],[(0,[z0,z2,z3,z4,z190,z5,z6]),(0,[z0,z2,z177,z3,z4,z5,z6]),(1,[z0,z191,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z192,z5,z6]),(0,[z193,z0,z2,z3,z4,z5,z6]),(0,[z45,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z6,z43]),(0,[z0,z2,z3,z4,z5,z194,z195])]],
   [[(0,[z196,z0,z2,z3,z4,z5,z6]),(0,[z197,z0,z2,z16,z4,z5,z6]),(0,[z0,z3,z16,z4,z63,z5,z6]),(0,[z198,z0,z2,z3,z4,z5,z6])],[(0,[z199,z0,z2,z3,z4,z5,z6]),(0,[z0,z200,z2,z3,z4,z5,z6]),(0,[z201,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z30,z6]),(1,[z49,z0,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z202,z6]),(0,[z49,z0,z2,z4,z5,z104,z6]),(1,[z109,z0,z2,z4,z124,z6]),(0,[z0,z2,z3,z203,z4,z5,z6]),(0,[z165,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z86])],[(0,[z0,z38,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z204]),(0,[z0,z2,z3,z4,z5,z6,z205]),(0,[z0,z2,z3,z4,z5,z6,z206]),(0,[z0,z207,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z3,z4,z5,z6]),(0,[z209,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z210,z3,z4,z5,z6]),(0,[z29,z2,z3,z4,z5,z6,z32]),(0,[z0,z2,z3,z211,z4,z5,z6]),(0,[z45,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z212]),(0,[z0,z2,z3,z23,z5,z6,z43])],[(0,[z58,z0,z3,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z213,z6]),(0,[z0,z2,z3,z4,z5,z214,z6]),(0,[z0,z2,z16,z4,z31,z5,z6]),(0,[z0,z2,z3,z62,z4,z5,z6]),(0,[z0,z215,z2,z3,z4,z5,z6])],[(0,[z0,z2,z216,z3,z4,z5,z6]),(0,[z0,z2,z217,z3,z4,z5,z6])],[(0,[z49,z0,z2,z9,z4,z5,z6]),(0,[z218,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z16,z4,z5,z68,z6]),(0,[z219,z0,z2,z3,z4,z5,z6]),(0,[z49,z220,z0,z2,z4,z5,z6]),(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z0,z38,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z43,z195])],[(0,[z222,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z223,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z224,z6]),(1,[z0,z61,z2,z4,z5,z88]),(0,[z0,z2,z3,z4,z5,z225,z6]),(0,[z100,z2,z3,z4,z5,z182,z6])],[(0,[z0,z2,z3,z4,z226,z5,z6]),(0,[z0,z2,z227,z3,z4,z5,z6]),(0,[z0,z228,z2,z3,z4,z5,z6]),(1,[z0,z229,z3,z4,z5,z6]),(0,[z230,z0,z2,z3,z4,z5,z6]),(0,[z231,z0,z2,z3,z4,z5,z137])],[(0,[z65,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z232]),(0,[z100,z0,z2,z3,z4,z5,z6])],[],[(0,[z233,z0,z2,z3,z4,z5,z6]),(0,[z193,z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z234,z5,z6]),(0,[z79,z0,z2,z3,z4,z5,z184]),(0,[z0,z2,z3,z4,z5,z6,z235]),(1,[z0,z2,z236,z4,z5,z6]),(0,[z0,z2,z3,z4,z237,z5,z6]),(0,[z0,z238,z2,z3,z4,z5,z6]),(1,[z0,z2,z239,z4,z5,z6])],[(0,[z0,z240,z2,z3,z4,z5,z6]),(0,[z198,z49,z0,z2,z4,z5,z6]),(0,[z241,z2,z3,z4,z5,z104,z6])],[(0,[z0,z2,z16,z4,z5,z242,z6]),(0,[z0,z228,z2,z3,z4,z5,z75]),(0,[z0,z2,z3,z4,z243,z5,z6])]],
   [[(0,[z79,z29,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z244,z4,z5,z6]),(0,[z0,z245,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z246]),(0,[z231,z0,z2,z3,z4,z5,z151]),(0,[z0,z2,z247,z3,z4,z5,z6])],[(0,[z29,z0,z2,z16,z4,z5,z6]),(0,[z0,z248,z2,z3,z4,z5,z6]),(1,[z65,z49,z0,z4,z5,z6]),(0,[z49,z0,z38,z2,z4,z5,z6]),(1,[z0,z2,z249,z4,z5,z6]),(0,[z0,z2,z3,z250,z4,z5,z6]),(0,[z94,z0,z2,z3,z92,z5,z6]),(0,[z0,z2,z3,z4,z182,z6,z195])],[(0,[z0,z2,z3,z4,z5,z251,z6]),(0,[z49,z0,z2,z4,z31,z5,z6]),(0,[z0,z2,z3,z252,z4,z5,z6]),(0,[z45,z49,z0,z2,z4,z5,z6]),(1,[z221,z0,z2,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z253,z6])],[(0,[z0,z2,z3,z4,z5,z6,z254]),(0,[z0,z2,z3,z4,z5,z255,z6]),(0,[z49,z0,z2,z4,z5,z68,z6]),(0,[z155,z0,z215,z3,z4,z5,z6])],[(0,[z0,z2,z256,z3,z4,z5,z6]),(0,[z0,z2,z3,z257,z4,z5,z6]),(0,[z79,z110,z2,z3,z4,z5,z6]),(0,[z258,z49,z0,z2,z4,z5,z6]),(1,[z0,z2,z177,z4,z5,z6]),(0,[z259,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z260,z6])],[(0,[z0,z2,z3,z4,z261,z5,z6]),(0,[z0,z2,z16,z4,z5,z124,z6]),(0,[z0,z74,z2,z262,z4,z5,z6]),(0,[z155,z0,z3,z4,z5,z263,z6]),(0,[z264,z0,z2,z3,z4,z5,z6]),(1,[z0,z265,z3,z4,z5,z6]),(0,[z0,z2,z3,z89,z23,z5,z6]),(0,[z0,z2,z3,z4,z5,z266,z6]),(0,[z0,z2,z3,z4,z136,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z5,z267]),(0,[z0,z2,z3,z4,z268,z5,z6]),(0,[z0,z2,z16,z269,z4,z5,z6]),(0,[z270,z0,z2,z3,z4,z5,z6]),(0,[z0,z271,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z80,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z6]),(0,[z272,z0,z2,z3,z4,z5,z6]),(0,[z65,z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z273,z6]),(0,[z0,z274,z2,z3,z4,z5,z6]),(0,[z275,z0,z2,z3,z89,z5,z6])],[(0,[z0,z2,z276,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z277]),(0,[z49,z49,z0,z2,z4,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z75]),(0,[z0,z2,z3,z4,z278,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z6])],[(0,[z0,z2,z3,z4,z5,z279,z6]),(0,[z259,z0,z38,z3,z4,z5,z6]),(0,[z0,z280,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z23,z99,z6]),(0,[z281,z0,z2,z3,z4,z5,z6])],[(0,[z66,z0,z3,z16,z4,z5,z6]),(0,[z0,z282,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z122]),(0,[z283,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z284,z6])],[(0,[z0,z2,z3,z4,z5,z285,z6]),(0,[z0,z2,z3,z4,z5,z286,z6]),(0,[z287,z0,z2,z3,z4,z5,z6]),(0,[z155,z0,z3,z16,z4,z5,z6]),(1,[z0,z2,z250,z4,z5,z6]),(0,[z40,z0,z2,z97,z4,z5,z6])],[(0,[z0,z20,z2,z16,z4,z5,z6]),(0,[z49,z0,z2,z4,z288,z5,z6]),(0,[z0,z2,z3,z4,z5,z32,z43]),(0,[z49,z0,z2,z4,z289,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z290]),(0,[z291,z0,z2,z3,z4,z5,z6])],[(0,[z292,z40,z2,z3,z4,z5,z6]),(0,[z293,z0,z2,z3,z4,z5,z6]),(0,[z165,z0,z3,z4,z5,z104,z6]),(0,[z275,z0,z2,z3,z4,z5,z43]),(0,[z294,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z295,z0,z2,z3,z4,z5,z6]),(0,[z296,z0,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z297]),(0,[z0,z2,z3,z4,z99,z5,z6])],[(0,[z49,z0,z2,z17,z4,z5,z6]),(0,[z29,z0,z2,z171,z4,z5,z6]),(0,[z49,z0,z2,z4,z18,z5,z6]),(0,[z0,z2,z3,z4,z63,z5,z6]),(1,[z0,z2,z298,z4,z5,z6])],[(0,[z0,z2,z3,z299,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z300,z6]),(0,[z0,z2,z3,z4,z301,z5,z6]),(0,[z45,z0,z2,z96,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z302])],[(1,[z0,z87,z16,z4,z5,z6]),(0,[z0,z2,z3,z303,z4,z5,z6]),(0,[z304,z0,z2,z3,z4,z5,z6])],[(0,[z193,z2,z3,z4,z5,z6,z32]),(0,[z49,z0,z2,z4,z5,z124,z6]),(0,[z0,z265,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z305])],[(0,[z306,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z307,z4,z5,z6]),(1,[z308,z0,z2,z4,z5,z6])],[(0,[z309,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z310,z5,z6])]],
   [[(0,[z58,z2,z3,z17,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z312,z0,z2,z4,z5,z104,z6]),(0,[z0,z2,z3,z4,z92,z5,z6])],[(0,[z313,z0,z2,z3,z4,z5,z6]),(0,[z8,z0,z2,z3,z4,z5,z6]),(0,[z0,z314,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z315]),(0,[z0,z2,z16,z4,z5,z316,z6]),(0,[z0,z2,z16,z4,z5,z194,z6]),(0,[z0,z2,z16,z4,z5,z6,z41]),(0,[z0,z2,z3,z4,z317,z5,z6]),(0,[z45,z0,z2,z3,z318,z5,z6]),(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z231,z0,z2,z3,z23,z5,z6]),(0,[z0,z2,z3,z4,z5,z320,z104])],[(0,[z0,z2,z3,z4,z5,z321,z6]),(0,[z0,z2,z3,z4,z5,z6,z322]),(0,[z0,z2,z3,z323,z4,z5,z6]),(0,[z324,z0,z2,z3,z4,z5,z6]),(0,[z241,z0,z2,z3,z4,z5,z6])],[(0,[z29,z0,z2,z236,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z325,z6]),(0,[z0,z2,z16,z4,z5,z263,z6]),(0,[z40,z207,z2,z3,z4,z5,z6]),(0,[z40,z0,z191,z3,z4,z5,z6]),(0,[z0,z2,z326,z3,z4,z5,z6]),(1,[z312,z0,z2,z4,z5,z6])],[(0,[z0,z20,z2,z158,z4,z5,z6]),(0,[z327,z0,z2,z3,z4,z5,z6]),(0,[z11,z49,z0,z2,z4,z5,z6]),(0,[z115,z0,z2,z3,z4,z5,z75])],[(0,[z0,z328,z2,z3,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z5,z68]),(0,[z0,z2,z3,z5,z104,z6,z43])],[(0,[z121,z0,z2,z3,z4,z5,z325]),(0,[z0,z2,z16,z97,z4,z5,z6]),(0,[z329,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z41])],[(0,[z330,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z331,z4,z5,z6]),(1,[z155,z0,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z332,z6]),(1,[z45,z0,z2,z318,z5,z6]),(0,[z103,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z333,z6]),(0,[z0,z2,z3,z4,z5,z334,z6]),(0,[z0,z2,z4,z5,z335,z104,z6])],[(0,[z0,z2,z3,z4,z5,z6,z78]),(0,[z193,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z336,z6])],[(0,[z337,z0,z2,z3,z4,z5,z6]),(0,[z29,z2,z3,z80,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z32]),(0,[z0,z2,z3,z338,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z339,z6]),(0,[z0,z2,z3,z4,z5,z340,z6])],[],[(0,[z0,z341,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z342,z4,z5,z6]),(0,[z220,z0,z2,z3,z4,z5,z6]),(0,[z0,z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z343,z6])],[(0,[z0,z344,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z345,z4,z5,z6]),(0,[z0,z2,z16,z4,z318,z5,z6]),(0,[z0,z2,z346,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z347,z5,z6]),(0,[z348,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z195]),(0,[z0,z349,z2,z3,z4,z5,z6])],[(0,[z350,z0,z1,z3,z4,z5,z6]),(0,[z351,z0,z2,z3,z4,z5,z6]),(0,[z0,z352,z2,z3,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z316,z6]),(0,[z49,z0,z2,z4,z5,z6,z41])],[(0,[z0,z215,z2,z16,z4,z5,z6]),(0,[z0,z2,z16,z4,z353,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z88]),(0,[z0,z354,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z355,z4,z5,z6]),(0,[z356,z0,z2,z3,z4,z5,z6]),(0,[z357,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z358]),(0,[z0,z2,z3,z4,z5,z6,z359]),(0,[z0,z2,z360,z3,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z5,z182])],[(0,[z0,z2,z16,z361,z4,z5,z6]),(0,[z0,z2,z3,z4,z362,z5,z6]),(0,[z45,z0,z2,z4,z318,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z363,z0,z2,z3,z4,z5,z6]),(0,[z0,z364,z2,z3,z4,z5,z6]),(0,[z365,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z366]),(0,[z155,z0,z3,z62,z4,z5,z6]),(0,[z155,z0,z2,z3,z4,z12,z6]),(0,[z109,z0,z38,z2,z4,z5,z6])],[(0,[z367,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z228,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z369,z5,z6]),(0,[z0,z2,z370,z3,z4,z5,z6]),(0,[z45,z0,z2,z3,z97,z5,z6]),(0,[z231,z0,z2,z3,z5,z104,z6]),(0,[z0,z371,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z372]),(0,[z0,z2,z3,z4,z5,z373,z6])],[(0,[z374,z0,z2,z3,z4,z5,z6]),(1,[z79,z2,z3,z288,z5,z6]),(0,[z0,z2,z3,z4,z375,z5,z6]),(0,[z0,z376,z2,z3,z4,z5,z6]),(0,[z49,z22,z0,z2,z4,z5,z6]),(0,[z0,z74,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z377,z6]),(0,[z378,z0,z2,z3,z4,z5,z6])],[(1,[z0,z74,z3,z62,z5,z6]),(0,[z0,z2,z3,z379,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z380,z6]),(0,[z0,z3,z4,z5,z381,z104,z6])]],
   [[(0,[z0,z382,z2,z3,z4,z5,z6]),(0,[z350,z0,z2,z3,z4,z5,z6]),(0,[z0,z383,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z384]),(1,[z0,z385,z2,z4,z5,z6])],[(0,[z79,z2,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z288,z5,z6]),(0,[z21,z0,z2,z16,z4,z5,z6]),(0,[z49,z21,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z73,z5,z6]),(0,[z0,z386,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z387,z4,z5,z6]),(0,[z388,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z389,z6]),(0,[z0,z1,z2,z97,z4,z5,z6]),(0,[z0,z390,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z391,z5,z6]),(0,[z0,z2,z3,z4,z392,z5,z6]),(0,[z0,z87,z2,z3,z4,z5,z6]),(0,[z0,z393,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z394,z6])],[(0,[z0,z395,z2,z3,z4,z5,z6]),(0,[z396,z0,z2,z3,z4,z5,z6]),(0,[z0,z38,z2,z3,z4,z124,z6])],[(0,[z58,z0,z2,z3,z4,z5,z267]),(0,[z0,z2,z3,z17,z4,z5,z6]),(0,[z66,z21,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z239,z4,z5,z6]),(0,[z0,z2,z3,z4,z18,z5,z6]),(0,[z0,z2,z3,z397,z4,z5,z6])],[(0,[z0,z2,z9,z4,z5,z124,z6]),(0,[z0,z1,z2,z16,z4,z5,z6]),(0,[z0,z2,z16,z4,z12,z5,z6]),(0,[z11,z0,z2,z3,z62,z5,z6]),(0,[z0,z2,z3,z4,z398,z5,z6]),(0,[z399,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z4,z5,z88,z6]),(1,[z0,z2,z3,z4,z5,z320])],[(0,[z0,z2,z3,z4,z400,z5,z6]),(0,[z0,z2,z3,z4,z5,z401,z6]),(0,[z0,z2,z3,z89,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z402,z6]),(0,[z0,z2,z403,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z404,z5,z6])]],
   [[(1,[z0,z395,z2,z4,z5,z6]),(0,[z405,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z9,z4,z5,z6,z32]),(0,[z0,z2,z3,z249,z4,z5,z6]),(0,[z0,z2,z3,z406,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z0,z407,z2,z3,z4,z5,z6]),(1,[z49,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z408,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z68]),(1,[z0,z74,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z47]),(0,[z275,z49,z0,z2,z4,z5,z6]),(0,[z409,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z89,z4,z136,z5])],[(0,[z0,z2,z3,z4,z410,z5,z6]),(0,[z258,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z411,z3,z4,z5,z6]),(0,[z412,z0,z2,z3,z4,z5,z6])],[(0,[z193,z1,z2,z3,z4,z5,z6]),(0,[z0,z48,z2,z16,z4,z5,z6]),(0,[z0,z413,z2,z3,z4,z5,z6]),(1,[z155,z0,z3,z4,z263,z6]),(0,[z0,z2,z3,z4,z414,z5,z6]),(0,[z45,z109,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z415,z5,z6])],[(0,[z0,z2,z3,z4,z5,z416,z6]),(0,[z79,z0,z2,z3,z288,z5,z6]),(0,[z79,z2,z3,z4,z288,z5,z6]),(0,[z0,z2,z3,z4,z5,z417,z6]),(0,[z0,z2,z3,z4,z5,z6,z418]),(0,[z0,z2,z3,z4,z5,z6,z419])],[(1,[z0,z383,z2,z4,z5,z6]),(0,[z420,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z61,z2,z4,z5,z6]),(0,[z421,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z422,z5,z6]),(0,[z0,z423,z2,z3,z4,z5,z6])],[(0,[z0,z2,z424,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z49,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z6,z43])]],
   [[(1,[z66,z20,z3,z4,z5,z6]),(0,[z2,z3,z4,z31,z5,z30,z6]),(0,[z0,z2,z97,z4,z18,z5,z6]),(0,[z0,z2,z3,z425,z4,z5,z6]),(0,[z426,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z427,z3,z4,z5,z6])],[(0,[z79,z0,z2,z3,z4,z5,z186]),(0,[z0,z2,z16,z4,z5,z182,z6]),(0,[z0,z428,z2,z3,z4,z5,z6]),(0,[z0,z429,z2,z3,z4,z5,z6])],[(0,[z49,z0,z2,z4,z5,z430,z6]),(0,[z115,z133,z2,z3,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z6,z195])],[(0,[z193,z8,z2,z3,z4,z5,z6]),(1,[z110,z2,z3,z80,z5,z6]),(0,[z0,z2,z3,z4,z5,z88,z6])],[(0,[z0,z215,z2,z3,z4,z263,z6]),(0,[z0,z431,z2,z3,z4,z5,z6])],[(0,[z0,z2,z432,z3,z4,z5,z6]),(0,[z155,z0,z2,z249,z4,z5,z6]),(0,[z433,z0,z2,z3,z4,z5,z6]),(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z435,z6]),(0,[z436,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z437,z3,z4,z5,z6])],[(0,[z0,z438,z2,z3,z4,z5,z6]),(0,[z439,z0,z2,z3,z4,z5,z6])],[(0,[z110,z0,z2,z3,z288,z5,z6]),(0,[z0,z2,z3,z4,z5,z440,z6]),(0,[z0,z441,z2,z3,z4,z5,z6]),(1,[z0,z2,z262,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z442,z6]),(0,[z0,z2,z3,z4,z5,z443,z6]),(0,[z444,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z445,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z446]),(0,[z0,z2,z3,z4,z447,z5,z6]),(0,[z0,z2,z3,z298,z4,z5,z6]),(0,[z448,z0,z2,z3,z4,z5,z6]),(0,[z231,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z449]),(0,[z450,z0,z2,z3,z4,z5,z6]),(0,[z115,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z451,z6])],[(1,[z22,z2,z3,z4,z5,z32]),(1,[z0,z228,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z452])],[(0,[z453,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z454,z3,z4,z5,z6]),(0,[z8,z0,z2,z16,z4,z5,z6]),(0,[z455,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z381,z6]),(0,[z0,z2,z3,z4,z5,z335,z6])],[(0,[z0,z2,z9,z97,z4,z5,z6]),(0,[z65,z49,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z456])],[(0,[z0,z2,z3,z4,z5,z316,z68]),(0,[z0,z228,z3,z4,z5,z316,z6]),(0,[z0,z2,z3,z4,z5,z6,z457])],[(0,[z121,z0,z2,z3,z4,z31,z6]),(0,[z0,z2,z3,z4,z5,z68,z43]),(0,[z458,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z459,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z182,z6]),(0,[z94,z0,z2,z3,z4,z136,z6])],[(0,[z0,z2,z16,z23,z4,z5,z6]),(0,[z221,z0,z74,z2,z4,z5,z6]),(0,[z0,z2,z97,z4,z5,z88,z6]),(0,[z292,z0,z2,z3,z4,z5,z6]),(0,[z460,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z89,z5,z194,z6])]],
   [[(0,[z0,z2,z461,z3,z4,z5,z6]),(0,[z0,z462,z2,z3,z4,z5,z6]),(0,[z463,z0,z2,z3,z4,z5,z6]),(0,[z0,z464,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z465,z6]),(0,[z0,z2,z3,z4,z5,z6,z466])],[(0,[z121,z0,z2,z3,z4,z30,z6]),(0,[z330,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z467,z5,z6]),(0,[z308,z0,z2,z3,z4,z5,z6])],[(0,[z46,z0,z2,z3,z4,z5,z6]),(0,[z468,z0,z2,z3,z4,z5,z6]),(0,[z29,z21,z2,z3,z4,z5,z6]),(1,[z11,z0,z3,z63,z5,z6])],[(1,[z0,z2,z3,z4,z5,z325]),(0,[z0,z2,z3,z469,z4,z5,z6]),(0,[z470,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z471,z6])],[],[(0,[z472,z0,z2,z3,z4,z5,z6]),(0,[z0,z74,z2,z3,z62,z5,z6]),(0,[z0,z2,z3,z4,z5,z473,z6]),(0,[z0,z474,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z475]),(1,[z0,z2,z3,z13,z5,z6])],[(1,[z193,z1,z2,z4,z5,z6]),(0,[z2,z3,z80,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z476]),(0,[z231,z49,z0,z2,z4,z5,z6]),(0,[z477,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z478,z6]),(0,[z0,z2,z3,z4,z479,z5,z6]),(0,[z0,z2,z3,z4,z5,z480,z6])],[(0,[z58,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z30,z6]),(1,[z0,z38,z2,z4,z18,z6]),(0,[z231,z0,z2,z3,z4,z99,z6]),(1,[z0,z2,z4,z5,z335,z6]),(0,[z0,z2,z3,z4,z5,z104,z6])]],
   [[(0,[z481,z0,z2,z3,z4,z5,z6])],[(0,[z110,z0,z383,z2,z4,z5,z6]),(0,[z0,z50,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z482,z5,z6]),(0,[z0,z2,z3,z4,z5,z194,z182])],[(0,[z0,z483,z2,z3,z4,z5,z6]),(0,[z264,z0,z215,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z484]),(1,[z103,z0,z2,z3,z4,z5])],[(0,[z485,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z2,z23,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z5,z6]),(1,[z94,z0,z2,z3,z4,z195])],[(0,[z0,z2,z3,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z486,z5,z6]),(0,[z487,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z488,z6]),(0,[z49,z0,z2,z96,z4,z5,z6]),(0,[z0,z2,z3,z4,z489,z5,z6]),(0,[z0,z2,z3,z4,z5,z490,z6])],[(0,[z491,z0,z2,z3,z4,z5,z6]),(0,[z176,z0,z2,z16,z4,z5,z6]),(0,[z492,z0,z2,z3,z4,z5,z6]),(0,[z493,z0,z2,z3,z4,z5,z6]),(1,[z470,z0,z2,z4,z5,z6]),(0,[z275,z0,z2,z3,z5,z6,z43])],[(0,[z0,z1,z67,z3,z4,z5,z6]),(0,[z0,z2,z96,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z494,z6]),(0,[z0,z2,z3,z23,z99,z5,z6])]],
   [[(1,[z0,z2,z495,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z122]),(0,[z496,z0,z2,z3,z4,z5,z6]),(0,[z0,z74,z2,z16,z4,z5,z6]),(0,[z46,z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z497,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z498,z5,z6]),(0,[z231,z0,z2,z3,z4,z104,z6])],[(0,[z0,z2,z3,z4,z5,z6,z499])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z500]),(0,[z2,z3,z80,z4,z288,z5,z6]),(0,[z0,z38,z2,z3,z4,z18,z6]),(0,[z501,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z502])],[(0,[z21,z2,z3,z9,z4,z5,z6]),(0,[z49,z0,z228,z2,z4,z5,z6]),(0,[z115,z0,z2,z239,z4,z5,z6]),(0,[z503,z0,z2,z3,z4,z5,z6])],[(0,[z58,z0,z395,z2,z4,z5,z6]),(0,[z504,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z505,z6]),(0,[z0,z2,z16,z16,z4,z5,z6]),(0,[z506,z0,z2,z3,z4,z5,z6]),(0,[z477,z49,z0,z2,z4,z5,z6]),(0,[z0,z215,z3,z4,z12,z5,z6]),(0,[z0,z2,z3,z4,z5,z507,z6])],[(0,[z40,z0,z2,z3,z4,z5,z41])],[(0,[z0,z2,z3,z4,z508,z5,z6]),(0,[z509,z0,z2,z3,z4,z5,z6]),(0,[z0,z385,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z510,z6]),(0,[z312,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z320,z6])],[(0,[z11,z0,z2,z511,z4,z5,z6]),(0,[z512,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z513])]],
   [[(0,[z0,z2,z3,z4,z5,z514,z6]),(0,[z0,z2,z3,z4,z31,z5,z6]),(0,[z0,z515,z2,z3,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z6,z32]),(0,[z0,z516,z2,z3,z4,z5,z6])],[(0,[z66,z0,z3,z17,z4,z5,z6]),(0,[z45,z0,z2,z16,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z194,z6]),(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z517,z5,z6]),(0,[z0,z2,z3,z4,z518,z5,z6])],[(0,[z0,z519,z2,z3,z4,z5,z6]),(1,[z0,z16,z4,z12,z5,z6]),(0,[z65,z0,z3,z4,z12,z5,z6]),(0,[z49,z0,z2,z4,z5,z90,z6]),(0,[z94,z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z520,z6]),(0,[z0,z521,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z136,z5,z195])],[(0,[z0,z2,z3,z4,z5,z68,z6]),(0,[z49,z0,z2,z4,z5,z263,z6]),(0,[z94,z275,z0,z2,z3,z4,z5]),(0,[z0,z522,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z523])],[(0,[z0,z2,z3,z4,z524,z5,z6]),(0,[z218,z0,z2,z16,z4,z5,z6]),(0,[z492,z49,z0,z2,z4,z5,z6])],[(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z525,z5,z6]),(0,[z0,z38,z2,z16,z4,z5,z6]),(1,[z0,z413,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z526])],[(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z20,z2,z4,z5,z6]),(0,[z21,z2,z3,z4,z31,z5,z6]),(0,[z0,z2,z527,z3,z4,z5,z6]),(0,[z65,z0,z87,z3,z4,z5,z6]),(0,[z49,z0,z2,z97,z4,z5,z6]),(0,[z0,z215,z2,z3,z4,z12,z6]),(0,[z0,z2,z3,z4,z528,z5,z6])],[(0,[z49,z0,z87,z2,z4,z5,z6]),(0,[z0,z2,z227,z16,z4,z5,z6]),(0,[z529,z0,z2,z3,z4,z5,z6]),(0,[z155,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z530]),(0,[z0,z2,z531,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z137,z6]),(0,[z275,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z29,z2,z3,z4,z5,z30,z6]),(0,[z0,z2,z3,z4,z5,z532,z6]),(0,[z65,z0,z2,z16,z4,z5,z6]),(0,[z0,z229,z2,z3,z4,z5,z6])],[(0,[z22,z2,z3,z4,z5,z6,z32]),(0,[z49,z0,z2,z16,z4,z5,z6]),(0,[z533,z0,z2,z3,z4,z5,z6]),(0,[z0,z38,z534,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z535,z6]),(0,[z0,z2,z3,z4,z5,z242,z6]),(0,[z0,z2,z3,z4,z5,z536,z6]),(0,[z0,z2,z3,z89,z4,z5,z194])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z537,z6]),(0,[z49,z121,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z32,z75]),(0,[z0,z240,z2,z16,z4,z5,z6]),(0,[z538,z0,z2,z3,z4,z5,z6]),(0,[z275,z0,z2,z3,z4,z136,z5])],[(0,[z539,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z289,z5,z6]),(0,[z0,z2,z3,z4,z5,z540,z6])],[(0,[z49,z0,z2,z4,z5,z6,z32]),(0,[z94,z0,z2,z3,z4,z5,z32]),(0,[z49,z0,z2,z4,z318,z5,z6]),(0,[z0,z2,z3,z541,z4,z5,z6])],[(0,[z0,z2,z542,z3,z4,z5,z6]),(0,[z0,z2,z3,z543,z4,z5,z6]),(0,[z544,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z111,z4,z5,z6]),(0,[z49,z115,z0,z2,z4,z5,z6]),(0,[z0,z2,z545,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z546])],[(0,[z0,z2,z3,z4,z5,z547,z6]),(0,[z548,z0,z2,z3,z4,z5,z6]),(0,[z0,z549,z2,z3,z4,z5,z6]),(0,[z40,z0,z265,z3,z4,z5,z6]),(0,[z550,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z551,z0,z2,z3,z4,z5,z6])],[],[(1,[z8,z2,z9,z4,z5,z6]),(0,[z65,z155,z0,z3,z4,z5,z6]),(0,[z0,z552,z2,z3,z4,z5,z6]),(0,[z553,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z124,z6]),(0,[z0,z2,z3,z4,z5,z6,z151])],[(1,[z58,z0,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z554,z5,z6]),(0,[z0,z2,z3,z269,z4,z5,z6]),(0,[z49,z155,z0,z2,z4,z5,z6]),(0,[z555,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z556]),(1,[z275,z0,z2,z3,z5,z43])],[(0,[z0,z2,z3,z4,z5,z6,z557]),(0,[z49,z8,z0,z2,z4,z5,z6]),(0,[z0,z2,z236,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z88,z6,z41]),(0,[z2,z3,z4,z5,z24,z104,z6]),(0,[z0,z2,z3,z4,z136,z182,z6])],[(0,[z21,z2,z3,z17,z4,z5,z6]),(0,[z0,z558,z2,z3,z4,z5,z6]),(1,[z0,z215,z3,z4,z12,z6]),(0,[z0,z2,z3,z4,z5,z559,z6]),(0,[z0,z2,z3,z4,z5,z560,z6])],[(0,[z561,z0,z2,z3,z4,z5,z6]),(0,[z22,z0,z2,z16,z4,z5,z6]),(0,[z272,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z262,z4,z5,z6]),(0,[z115,z0,z228,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z42])],[(0,[z562,z0,z2,z3,z4,z5,z6]),(0,[z79,z0,z2,z3,z4,z5,z6]),(0,[z0,z563,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z564,z5,z6]),(0,[z565,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z16,z89,z4,z5,z6]),(0,[z566,z0,z2,z3,z4,z5,z6]),(0,[z45,z0,z229,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z381,z6])],[(0,[z0,z2,z3,z4,z5,z6,z567]),(0,[z0,z2,z3,z4,z568,z5,z6]),(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z570,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z96,z97,z5,z6]),(0,[z109,z0,z2,z4,z5,z124,z6]),(0,[z0,z2,z3,z5,z194,z6,z43])],[(1,[z350,z0,z3,z4,z5,z6]),(0,[z0,z2,z16,z62,z4,z5,z6])],[(0,[z0,z571,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z184]),(0,[z11,z0,z2,z16,z4,z5,z6]),(0,[z45,z0,z56,z3,z4,z5,z6])],[(1,[z0,z2,z511,z4,z5,z6]),(0,[z115,z0,z2,z3,z4,z5,z316]),(0,[z0,z2,z96,z3,z318,z5,z6]),(1,[z2,z3,z4,z5,z6,z77])],[(0,[z0,z2,z3,z4,z5,z267,z6]),(0,[z572,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z136,z5,z68]),(0,[z0,z2,z3,z4,z573,z5,z6]),(0,[z49,z0,z2,z4,z12,z5,z6]),(1,[z0,z228,z3,z4,z5,z316]),(0,[z0,z2,z3,z574,z4,z5,z6])],[(0,[z94,z0,z2,z3,z13,z5,z6])],[(0,[z575,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z16,z4,z12,z5,z6]),(0,[z576,z0,z2,z3,z4,z5,z6]),(0,[z49,z109,z0,z2,z4,z5,z6]),(1,[z231,z0,z2,z3,z104,z6]),(0,[z0,z2,z3,z4,z577,z5,z6]),(1,[z0,z2,z3,z89,z5,z194]),(0,[z2,z3,z4,z5,z182,z6,z77])]],
   [[(0,[z578,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z579,z4,z5,z6]),(1,[z264,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z580,z5,z6])],[(0,[z8,z0,z1,z2,z4,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z6]),(1,[z0,z16,z4,z5,z6,z75])],[(0,[z581,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z582,z6])],[(0,[z58,z0,z2,z495,z4,z5,z6]),(0,[z29,z0,z2,z3,z4,z5,z6]),(0,[z583,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z316,z6]),(0,[z0,z2,z3,z4,z584,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z41]),(0,[z0,z2,z3,z4,z5,z194,z6])],[(0,[z585,z0,z2,z3,z4,z5,z6]),(0,[z79,z49,z0,z2,z4,z5,z6]),(0,[z586,z0,z2,z3,z4,z5,z6]),(0,[z11,z155,z0,z3,z4,z5,z6]),(0,[z587,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z588,z6])],[(0,[z0,z2,z3,z589,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z590,z6]),(0,[z0,z2,z3,z4,z5,z263,z6])],[(0,[z49,z0,z2,z62,z4,z5,z6]),(0,[z0,z591,z2,z3,z4,z5,z6])]],
   [[(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z593])],[(1,[z539,z0,z2,z4,z5,z6]),(0,[z594,z0,z2,z3,z4,z5,z6]),(0,[z595,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z596,z5,z6]),(0,[z0,z2,z3,z99,z5,z104,z6]),(0,[z0,z2,z3,z4,z136,z5,z182])],[(1,[z58,z3,z17,z4,z5,z6]),(0,[z49,z0,z215,z2,z4,z5,z6]),(0,[z597,z0,z2,z3,z4,z5,z6])],[(0,[z65,z58,z0,z3,z4,z5,z6]),(0,[z66,z2,z3,z4,z5,z6,z32]),(0,[z49,z0,z2,z223,z4,z5,z6]),(0,[z598,z0,z2,z3,z4,z5,z6]),(0,[z599,z0,z2,z3,z4,z5,z6]),(0,[z600,z0,z2,z3,z4,z5,z6]),(0,[z601,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z602,z4,z5,z6])],[(0,[z49,z58,z0,z2,z4,z5,z6]),(0,[z66,z20,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z603,z6]),(0,[z0,z2,z3,z4,z5,z604,z6]),(0,[z0,z2,z16,z4,z136,z5,z6]),(0,[z0,z215,z2,z250,z4,z5,z6]),(0,[z605,z0,z2,z3,z4,z5,z6]),(0,[z308,z0,z2,z4,z5,z6,z43])],[(0,[z58,z0,z3,z17,z4,z5,z6]),(0,[z0,z2,z3,z4,z606,z5,z6]),(0,[z65,z0,z74,z3,z4,z5,z6]),(0,[z576,z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z607,z4,z5,z6])],[(0,[z0,z2,z16,z80,z4,z5,z6]),(0,[z49,z0,z74,z2,z4,z5,z6]),(0,[z115,z0,z385,z2,z4,z5,z6])],[(0,[z0,z2,z3,z495,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z6,z75]),(0,[z0,z2,z96,z3,z97,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z182,z43])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z608]),(0,[z0,z228,z3,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z318,z5,z6])],[(0,[z0,z20,z2,z3,z4,z5,z6]),(0,[z609,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z610,z5,z6]),(0,[z611,z0,z2,z3,z4,z5,z6])],[(0,[z29,z49,z0,z2,z4,z5,z6]),(0,[z612,z0,z2,z3,z4,z5,z6]),(0,[z49,z0,z3,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z353,z5,z6]),(0,[z0,z2,z3,z4,z5,z613,z6])],[(0,[z0,z2,z3,z4,z614,z5,z6]),(0,[z0,z2,z3,z4,z615,z5,z6]),(0,[z0,z2,z3,z4,z5,z616,z6]),(0,[z40,z0,z2,z3,z4,z5,z6])],[(0,[z0,z617,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z618,z5,z6]),(0,[z0,z2,z3,z4,z619,z5,z6]),(0,[z0,z2,z3,z4,z5,z620,z6])],[(0,[z0,z2,z3,z4,z621,z5,z6]),(0,[z0,z2,z3,z361,z4,z5,z6]),(0,[z0,z2,z16,z4,z99,z5,z6]),(1,[z512,z2,z3,z4,z5,z6]),(0,[z0,z228,z2,z298,z4,z5,z6]),(0,[z0,z2,z3,z4,z622,z5,z6])],[(0,[z0,z2,z16,z4,z63,z5,z6])],[(0,[z0,z2,z3,z4,z5,z623,z6]),(0,[z0,z2,z16,z4,z301,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z624])]],
   [[(0,[z0,z2,z3,z4,z625,z5,z6]),(1,[z0,z2,z16,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z626,z6]),(0,[z275,z0,z2,z16,z4,z5,z6]),(0,[z49,z0,z2,z4,z136,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z627]),(0,[z628,z0,z2,z3,z4,z5,z6])],[(0,[z193,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z629,z6]),(1,[z241,z2,z3,z4,z5,z6])],[(0,[z539,z0,z20,z2,z4,z5,z6]),(0,[z49,z0,z2,z80,z4,z5,z6]),(0,[z630,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z62,z4,z12,z5,z6]),(0,[z631,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z632,z4,z5,z6]),(0,[z29,z0,z2,z3,z4,z30,z6]),(0,[z49,z0,z2,z4,z5,z6,z75]),(0,[z0,z2,z97,z4,z318,z5,z6]),(0,[z109,z0,z2,z3,z4,z124,z6]),(1,[z0,z534,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z633,z5,z6]),(0,[z634,z0,z2,z3,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z316,z32]),(0,[z0,z2,z3,z4,z5,z194,z32]),(0,[z0,z2,z3,z636,z4,z5,z6]),(0,[z0,z2,z3,z4,z637,z5,z6]),(0,[z65,z0,z228,z3,z4,z5,z6]),(0,[z115,z0,z3,z4,z5,z6,z75]),(0,[z0,z2,z3,z4,z5,z638,z6]),(0,[z0,z2,z3,z4,z5,z6,z43])],[(0,[z0,z2,z3,z4,z639,z5,z6]),(0,[z0,z3,z16,z4,z5,z6,z75]),(0,[z640,z0,z2,z3,z4,z5,z6]),(0,[z641,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z642,z5,z6])],[(0,[z643,z0,z2,z3,z4,z5,z6]),(0,[z193,z0,z2,z9,z4,z5,z6]),(0,[z45,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z68,z194]),(0,[z0,z87,z2,z16,z4,z5,z6]),(0,[z0,z644,z2,z3,z4,z5,z6]),(0,[z0,z74,z3,z62,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z645,z6]),(0,[z646,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z430,z6]),(0,[z11,z0,z74,z3,z4,z5,z6])],[(0,[z647,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z316,z6,z75]),(0,[z0,z2,z3,z4,z5,z6,z648])],[(0,[z0,z2,z3,z4,z649,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z650]),(0,[z49,z0,z2,z4,z99,z5,z6]),(0,[z0,z228,z2,z3,z4,z5,z316])],[(0,[z0,z2,z3,z4,z5,z6,z651]),(0,[z652,z0,z2,z3,z4,z5,z6]),(0,[z653,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z654]),(0,[z49,z0,z2,z4,z63,z5,z6]),(1,[z207,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z655,z5,z6]),(0,[z275,z0,z2,z3,z4,z5,z194]),(0,[z0,z2,z3,z4,z656,z5,z6])],[(0,[z657,z0,z2,z3,z4,z5,z6]),(0,[z0,z658,z2,z3,z4,z5,z6]),(0,[z0,z659,z2,z3,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z332,z6]),(0,[z11,z0,z2,z3,z63,z5,z6]),(0,[z660,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z661,z6]),(0,[z662,z0,z2,z3,z4,z5,z6]),(0,[z663,z0,z2,z3,z4,z5,z6])],[(0,[z664,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z111,z4,z5,z6]),(0,[z0,z2,z3,z665,z4,z5,z6]),(0,[z0,z2,z3,z666,z4,z5,z6]),(0,[z0,z2,z3,z667,z4,z5,z6]),(0,[z0,z2,z3,z4,z668,z5,z6])],[(1,[z0,z2,z158,z4,z5,z6]),(0,[z121,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z669]),(0,[z0,z2,z3,z4,z670,z5,z6])],[(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z49,z110,z0,z2,z4,z5,z6]),(0,[z153,z49,z0,z2,z4,z5,z6]),(0,[z671,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z672])]],
   [[(1,[z0,z2,z171,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z673,z6]),(0,[z674,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z675])],[(0,[z0,z676,z2,z3,z4,z5,z6]),(0,[z79,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z677,z4,z5,z6]),(0,[z0,z563,z2,z16,z4,z5,z6]),(0,[z155,z0,z413,z2,z4,z5,z6]),(0,[z0,z2,z3,z678,z4,z5,z6])],[(1,[z66,z0,z16,z4,z5,z6]),(0,[z679,z0,z2,z3,z4,z5,z6]),(1,[z21,z2,z3,z4,z5,z68]),(0,[z0,z2,z16,z4,z5,z6,z195]),(0,[z0,z2,z534,z3,z4,z5,z6]),(0,[z0,z680,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z681,z6]),(0,[z0,z2,z3,z4,z5,z68,z75]),(0,[z0,z2,z3,z4,z5,z6,z682]),(0,[z0,z2,z3,z683,z4,z5,z6])],[(0,[z2,z3,z17,z4,z5,z6,z32]),(0,[z21,z2,z3,z4,z5,z68,z6]),(0,[z0,z2,z3,z4,z684,z5,z6]),(0,[z685,z0,z2,z3,z4,z5,z6]),(0,[z0,z686,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z182,z6])],[(0,[z193,z21,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z12,z5,z263,z6]),(0,[z0,z2,z3,z4,z687,z5,z6]),(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z512,z115,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z689,z6]),(0,[z0,z2,z3,z4,z5,z6,z42])],[(0,[z58,z0,z2,z3,z4,z5,z78]),(0,[z0,z2,z3,z4,z5,z690,z6]),(0,[z0,z2,z3,z4,z691,z5,z6])],[(0,[z0,z2,z692,z3,z4,z5,z6]),(0,[z0,z693,z2,z3,z4,z5,z6]),(1,[z292,z2,z3,z4,z5,z6])]],
   [[(0,[z694,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z695,z4,z5,z6])],[(0,[z0,z2,z3,z4,z696,z5,z6]),(0,[z49,z0,z2,z2,z4,z5,z6]),(0,[z0,z2,z191,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z697,z5,z6]),(0,[z0,z2,z3,z4,z5,z186,z6]),(0,[z470,z0,z228,z2,z4,z5,z6]),(1,[z0,z56,z3,z4,z5,z6]),(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z699])],[(0,[z0,z700,z2,z3,z4,z5,z6]),(0,[z110,z0,z2,z16,z4,z5,z6]),(0,[z664,z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z511,z4,z5,z6])],[(0,[z21,z0,z2,z3,z4,z5,z6]),(1,[z259,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z701])],[(0,[z0,z702,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z703,z4,z5,z6]),(0,[z231,z0,z2,z16,z4,z5,z6]),(0,[z0,z2,z4,z18,z5,z124,z6])],[(0,[z0,z2,z16,z4,z288,z5,z6]),(0,[z197,z0,z2,z3,z4,z5,z6]),(0,[z155,z0,z2,z3,z4,z263,z6]),(0,[z0,z2,z3,z4,z5,z6,z704])],[(0,[z0,z2,z705,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z68,z6,z32]),(0,[z0,z2,z3,z4,z706,z5,z6]),(0,[z49,z0,z2,z4,z5,z6,z195]),(0,[z94,z0,z2,z3,z4,z5,z195])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z133,z2,z3,z4,z5,z6]),(0,[z2,z53,z3,z4,z5,z32]),(0,[z49,z0,z265,z4,z5,z6]),(0,[z11,z0,z3,z614,z5,z6]),(0,[z0,z2,z3,z707,z5,z6]),(0,[z0,z2,z4,z708,z5,z6]),(0,[z709,z2,z3,z4,z5,z6])],[(0,[z0,z700,z16,z4,z5,z6]),(0,[z221,z0,z229,z4,z5,z6]),(0,[z3,z4,z5,z381,z24,z6])],[(0,[z0,z2,z710,z4,z5,z6]),(0,[z0,z166,z16,z4,z5,z6]),(0,[z49,z0,z2,z92,z5,z6]),(0,[z0,z56,z4,z5,z88,z6]),(0,[z0,z2,z3,z4,z6,z711])],[(0,[z0,z2,z3,z4,z5,z712]),(0,[z66,z563,z3,z4,z5,z6]),(0,[z713,z0,z2,z3,z4,z6]),(0,[z220,z0,z16,z4,z5,z6]),(0,[z0,z714,z3,z4,z5,z6])],[(0,[z0,z715,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z716]),(0,[z0,z2,z227,z97,z5,z6]),(0,[z49,z717,z0,z4,z5,z6]),(0,[z49,z165,z0,z4,z5,z6]),(0,[z115,z0,z3,z4,z5,z718])],[(0,[z58,z0,z719,z4,z5,z6]),(0,[z2,z3,z4,z31,z5,z184]),(0,[z40,z0,z2,z4,z5,z41]),(0,[z0,z2,z4,z5,z6,z720])],[(0,[z0,z2,z721,z4,z5,z6]),(0,[z0,z659,z16,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z722]),(0,[z49,z0,z74,z62,z5,z6])],[(0,[z0,z2,z16,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z78])]],
   [[(0,[z0,z723,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z724]),(0,[z433,z0,z16,z4,z5,z6])],[(0,[z0,z725,z2,z4,z5,z6]),(0,[z66,z21,z16,z4,z5,z6]),(0,[z0,z726,z3,z4,z5,z6]),(0,[z0,z727,z2,z4,z5,z6]),(0,[z231,z0,z2,z16,z104,z6]),(0,[z0,z411,z16,z4,z5,z6]),(0,[z728,z2,z3,z4,z5,z6]),(0,[z729,z2,z3,z4,z5,z6]),(0,[z165,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z730,z6]),(0,[z0,z2,z4,z18,z731,z6])],[(0,[z1,z732,z2,z4,z5,z6]),(0,[z0,z733,z3,z4,z5,z6])],[(0,[z0,z734,z2,z4,z5,z6]),(0,[z0,z534,z3,z4,z5,z6]),(0,[z0,z250,z4,z12,z5,z6]),(0,[z45,z0,z2,z498,z5,z6]),(0,[z735,z0,z3,z4,z5,z6])],[(0,[z110,z0,z736,z4,z5,z6]),(0,[z2,z3,z4,z5,z737,z32]),(0,[z231,z49,z0,z2,z104,z6]),(0,[z0,z3,z4,z12,z738,z6]),(0,[z477,z0,z56,z4,z5,z6])],[(0,[z0,z424,z16,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z739]),(0,[z0,z2,z3,z92,z5,z32]),(0,[z740,z0,z2,z4,z5,z6]),(0,[z109,z0,z2,z4,z536,z6]),(0,[z0,z2,z96,z708,z5,z6])],[(0,[z741,z2,z3,z4,z5,z6]),(0,[z0,z38,z534,z4,z18,z6]),(0,[z742,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z743]),(0,[z0,z2,z3,z4,z744,z6]),(0,[z49,z0,z2,z4,z5,z137])]],
   [[(0,[z745,z0,z2,z4,z5,z6]),(0,[z0,z746,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z747,z6])],[(0,[z0,z2,z3,z748,z5,z6]),(0,[z8,z732,z2,z4,z5,z6]),(0,[z0,z2,z749,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z366]),(0,[z750,z0,z2,z4,z5,z6]),(0,[z0,z2,z751,z4,z5,z6]),(0,[z0,z752,z2,z4,z5,z6])],[(0,[z207,z2,z3,z4,z5,z6]),(0,[z0,z753,z3,z4,z5,z6]),(0,[z0,z191,z3,z4,z5,z6]),(0,[z49,z754,z2,z4,z5,z6]),(0,[z45,z207,z2,z4,z5,z6]),(0,[z275,z0,z2,z5,z42,z43])],[(0,[z79,z2,z3,z288,z5,z184]),(0,[z0,z437,z16,z4,z5,z6]),(0,[z0,z3,z62,z755,z5,z6]),(0,[z0,z3,z4,z5,z6,z718]),(0,[z165,z0,z3,z4,z5,z320])],[(0,[z0,z395,z16,z4,z5,z6]),(0,[z0,z16,z4,z375,z5,z6]),(0,[z595,z2,z3,z4,z5,z32]),(0,[z45,z0,z2,z517,z5,z6]),(0,[z0,z2,z4,z5,z731,z6])],[(0,[z0,z2,z3,z5,z6,z756]),(0,[z0,z686,z16,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z151]),(0,[z109,z0,z2,z4,z124,z6])],[(0,[z0,z2,z736,z4,z5,z6]),(0,[z664,z220,z2,z4,z5,z6])],[(0,[z0,z2,z757,z4,z5,z6]),(0,[z0,z2,z171,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z758]),(0,[z759,z0,z2,z4,z5,z6]),(0,[z0,z48,z2,z4,z353,z6]),(0,[z0,z61,z2,z4,z5,z430]),(0,[z0,z2,z3,z760,z5,z6]),(0,[z761,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z762,z6]),(0,[z0,z2,z3,z763,z5,z6])],[(0,[z0,z2,z764,z4,z5,z6]),(0,[z21,z2,z3,z4,z5,z68])],[(0,[z0,z2,z3,z4,z5,z765]),(0,[z0,z766,z3,z4,z5,z6]),(0,[z49,z0,z56,z4,z5,z6]),(0,[z767,z2,z3,z4,z5,z6]),(0,[z0,z768,z3,z4,z5,z6])],[(0,[z350,z0,z16,z4,z5,z6]),(0,[z769,z0,z236,z4,z5,z6]),(0,[z770,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z771,z6]),(0,[z0,z2,z3,z23,z5,z151]),(0,[z241,z3,z4,z5,z381,z6])],[(0,[z0,z2,z772,z4,z5,z6]),(0,[z717,z0,z16,z4,z5,z6]),(0,[z773,z2,z3,z4,z5,z6]),(0,[z492,z0,z2,z4,z90,z6]),(0,[z49,z2,z4,z5,z24,z6]),(0,[z49,z0,z2,z4,z136,z182]),(0,[z774,z2,z3,z4,z5,z6]),(0,[z775,z2,z3,z4,z5,z6]),(0,[z0,z2,z776,z4,z5,z6]),(0,[z155,z0,z3,z4,z738,z6]),(0,[z0,z777,z3,z4,z5,z6]),(0,[z778,z0,z2,z92,z5,z6]),(0,[z779,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z780]),(0,[z781,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z4,z5,z88]),(0,[z0,z4,z5,z782,z381,z6])],[(0,[z292,z2,z3,z4,z5,z6]),(0,[z441,z2,z9,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z184]),(0,[z420,z0,z16,z4,z5,z6]),(0,[z0,z229,z3,z4,z5,z6]),(0,[z0,z228,z16,z4,z5,z316]),(0,[z45,z0,z229,z318,z5,z6]),(0,[z0,z2,z97,z708,z5,z6]),(0,[z275,z0,z2,z3,z5,z783])],[(0,[z562,z2,z3,z4,z5,z32]),(0,[z0,z16,z4,z5,z6,z557]),(0,[z29,z49,z2,z4,z30,z6]),(0,[z49,z0,z531,z4,z5,z6]),(0,[z45,z0,z2,z289,z5,z6]),(0,[z784,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z227,z269,z5,z6]),(0,[z2,z16,z4,z5,z785,z6]),(0,[z0,z2,z16,z89,z5,z194])],[(0,[z199,z0,z16,z4,z5,z6]),(0,[z0,z16,z4,z410,z5,z6]),(0,[z66,z16,z4,z5,z6,z32]),(0,[z0,z2,z236,z4,z5,z6]),(0,[z0,z786,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z68,z737]),(0,[z0,z644,z16,z4,z5,z6]),(0,[z0,z56,z3,z4,z5,z6]),(0,[z0,z2,z239,z4,z5,z6]),(0,[z49,z0,z228,z4,z5,z316]),(0,[z0,z2,z787,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z788])],[(0,[z0,z789,z3,z4,z5,z6]),(0,[z0,z16,z4,z414,z5,z6]),(0,[z0,z240,z2,z4,z5,z242])],[(0,[z153,z0,z67,z4,z5,z6]),(0,[z82,z0,z3,z4,z5,z75]),(0,[z272,z0,z3,z4,z5,z75]),(0,[z103,z49,z0,z2,z4,z5])],[(0,[z0,z2,z3,z4,z5,z790]),(0,[z0,z16,z4,z422,z5,z6]),(0,[z94,z49,z0,z2,z4,z195]),(0,[z231,z241,z2,z3,z104,z6])],[(0,[z0,z2,z791,z4,z5,z6]),(0,[z110,z2,z3,z792,z5,z6]),(0,[z470,z0,z265,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z793]),(0,[z794,z0,z2,z4,z5,z6])],[(0,[z0,z2,z495,z4,z5,z78]),(0,[z221,z0,z2,z4,z5,z6]),(0,[z103,z165,z0,z3,z4,z5])],[(0,[z0,z2,z795,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z796]),(0,[z797,z0,z2,z4,z5,z6]),(0,[z798,z2,z3,z4,z5,z6])]],
   [[(0,[z799,z2,z3,z4,z5,z6])],[(0,[z176,z2,z9,z4,z5,z6]),(0,[z2,z3,z4,z5,z24,z6]),(0,[z0,z383,z736,z4,z5,z6]),(0,[z0,z800,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z737]),(0,[z801,z0,z2,z16,z4,z6])],[(0,[z0,z2,z802,z4,z5,z6]),(0,[z0,z72,z3,z4,z5,z316]),(0,[z0,z2,z177,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z803]),(0,[z109,z0,z534,z4,z5,z6])],[(0,[z0,z804,z2,z4,z5,z6]),(0,[z49,z110,z2,z80,z5,z6]),(0,[z29,z2,z3,z4,z30,z6]),(0,[z805,z2,z16,z4,z5,z6]),(0,[z0,z2,z806,z4,z5,z6]),(0,[z807,z0,z2,z4,z5,z6])],[(0,[z65,z0,z395,z4,z5,z6]),(0,[z196,z0,z16,z4,z5,z6])],[(0,[z0,z808,z2,z4,z5,z6]),(0,[z809,z0,z2,z4,z5,z6]),(0,[z810,z0,z2,z16,z5,z6]),(0,[z811,z0,z74,z4,z5,z6]),(0,[z0,z812,z2,z4,z5,z6]),(0,[z0,z813,z3,z4,z5,z6]),(0,[z94,z0,z2,z3,z13,z195])],[(0,[z0,z429,z16,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z814]),(0,[z49,z784,z2,z4,z5,z6]),(0,[z815,z2,z3,z4,z5,z6])],[(0,[z0,z719,z16,z4,z5,z6]),(0,[z22,z2,z3,z4,z5,z737]),(0,[z816,z0,z2,z4,z5,z6])]],
   [[(0,[z0,z817,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z122]),(0,[z399,z0,z16,z4,z5,z6]),(0,[z2,z3,z4,z136,z5,z77])],[(0,[z0,z67,z3,z4,z5,z6]),(0,[z0,z16,z4,z5,z381,z6]),(0,[z0,z2,z16,z13,z5,z6]),(0,[z0,z2,z250,z4,z5,z6]),(0,[z685,z49,z0,z4,z5,z6])],[(0,[z0,z2,z818,z4,z5,z6]),(0,[z717,z0,z87,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z819]),(0,[z0,z2,z820,z4,z5,z6])],[(0,[z609,z0,z16,z4,z5,z6]),(0,[z65,z0,z3,z4,z5,z78]),(0,[z0,z2,z692,z97,z5,z6]),(0,[z0,z38,z2,z4,z697,z6]),(0,[z0,z821,z3,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z457]),(0,[z0,z215,z3,z4,z738,z6])],[(0,[z2,z3,z80,z792,z5,z6])],[(0,[z0,z822,z2,z3,z4,z6]),(0,[z193,z732,z2,z4,z5,z6]),(0,[z0,z2,z16,z5,z823,z6]),(0,[z0,z2,z298,z4,z5,z6]),(0,[z49,z259,z0,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z824])],[(0,[z825,z0,z3,z4,z5,z6]),(0,[z512,z2,z16,z4,z5,z6]),(0,[z155,z0,z249,z4,z263,z6]),(0,[z0,z826,z3,z4,z5,z6]),(0,[z0,z826,z4,z5,z6,z43])],[(0,[z827,z2,z3,z4,z5,z6]),(0,[z0,z16,z4,z467,z5,z6]),(0,[z49,z0,z215,z4,z12,z6]),(0,[z0,z2,z3,z828,z5,z6]),(1,[z0,z2,z4,z731,z6]),(0,[z0,z2,z3,z4,z731,z6])]],
   [[(1,[z829,z3,z4,z5,z6]),(0,[z0,z2,z830,z4,z5,z6]),(0,[z100,z2,z3,z4,z5,z6]),(0,[z0,z2,z16,z5,z6,z722]),(0,[z49,z0,z229,z4,z5,z6])],[(0,[z0,z395,z2,z4,z5,z267]),(0,[z0,z831,z3,z4,z5,z6]),(0,[z29,z0,z832,z4,z5,z6]),(1,[z717,z0,z4,z5,z6])],[(0,[z833,z0,z2,z3,z4,z5]),(0,[z470,z0,z16,z4,z5,z6]),(0,[z103,z0,z2,z3,z92,z5])],[(0,[z241,z2,z16,z4,z5,z6]),(0,[z49,z100,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z834,z6])],[(0,[z21,z2,z3,z4,z5,z645]),(0,[z835,z2,z3,z4,z5,z6]),(0,[z0,z191,z4,z5,z6,z41])],[(0,[z0,z2,z3,z4,z836,z6]),(0,[z433,z2,z3,z4,z5,z32]),(0,[z0,z534,z16,z4,z5,z6]),(0,[z837,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z89,z5,z620])],[(0,[z49,z0,z2,z4,z5,z122]),(0,[z0,z838,z2,z4,z5,z6]),(0,[z40,z0,z191,z4,z5,z41])],[(0,[z0,z839,z3,z4,z5,z6]),(0,[z0,z74,z16,z63,z5,z6]),(0,[z0,z16,z4,z482,z5,z6]),(0,[z0,z2,z16,z4,z5,z840]),(0,[z0,z56,z96,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z841])]],
   [[(0,[z29,z2,z3,z4,z842,z6]),(1,[z0,z2,z3,z4,z711])],[(0,[z350,z0,z395,z4,z5,z6]),(0,[z319,z2,z9,z4,z5,z6]),(0,[z0,z431,z16,z4,z5,z6]),(0,[z49,z843,z2,z4,z5,z6]),(0,[z844,z2,z3,z4,z5,z6]),(0,[z207,z2,z97,z4,z5,z6]),(0,[z0,z191,z97,z4,z5,z6]),(0,[z845,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z846]),(0,[z155,z0,z16,z4,z12,z6]),(0,[z218,z0,z2,z301,z5,z6]),(0,[z847,z0,z2,z4,z5,z6])],[(0,[z492,z0,z16,z4,z5,z6]),(0,[z197,z0,z16,z4,z12,z6]),(0,[z275,z49,z0,z2,z5,z43]),(0,[z45,z0,z2,z318,z5,z6])],[(0,[z0,z2,z4,z5,z6,z848]),(0,[z207,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z137])],[(0,[z58,z393,z3,z4,z5,z6]),(0,[z0,z849,z3,z4,z5,z6]),(0,[z850,z0,z2,z4,z5,z6]),(0,[z2,z3,z80,z5,z106,z6]),(0,[z851,z0,z2,z4,z5,z6]),(0,[z0,z2,z852,z4,z5,z6])],[(0,[z119,z0,z16,z4,z5,z6]),(0,[z0,z2,z853,z4,z5,z6]),(0,[z0,z2,z854,z4,z5,z6]),(0,[z470,z0,z228,z4,z5,z316]),(0,[z0,z855,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z856,z6])],[(0,[z0,z857,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z858])]],
   [[(0,[z0,z2,z3,z4,z5,z859]),(0,[z0,z2,z3,z101,z5,z194]),(0,[z0,z74,z3,z323,z5,z6]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z133,z2,z3,z4,z5,z75]),(0,[z860,z2,z3,z4,z5,z6])],[(0,[z0,z67,z4,z5,z124,z6]),(0,[z0,z861,z2,z4,z5,z6]),(0,[z0,z2,z832,z4,z5,z6]),(0,[z0,z236,z832,z4,z5,z6]),(0,[z0,z413,z16,z4,z5,z6]),(0,[z862,z0,z2,z3,z4,z5]),(0,[z0,z2,z4,z18,z343,z6]),(0,[z0,z2,z3,z863,z4,z5])],[(0,[z477,z0,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z151])],[(0,[z0,z2,z3,z4,z864,z6]),(0,[z21,z2,z16,z4,z5,z68]),(0,[z365,z0,z16,z4,z5,z6]),(0,[z0,z2,z865,z4,z5,z6])],[(0,[z829,z2,z3,z4,z5,z6])],[(0,[z330,z563,z2,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z513]),(0,[z197,z0,z2,z4,z124,z6]),(0,[z11,z49,z0,z63,z5,z6]),(0,[z754,z2,z3,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z711])],[(0,[z487,z0,z16,z4,z5,z6]),(0,[z0,z2,z866,z4,z5,z6])],[]],
   [[(0,[z82,z0,z16,z4,z5,z6]),(0,[z0,z822,z2,z16,z4,z6]),(0,[z0,z2,z16,z4,z5,z867]),(0,[z292,z2,z16,z4,z5,z6]),(0,[z512,z2,z239,z4,z5,z6])],[(0,[z66,z2,z3,z4,z5,z78]),(0,[z49,z21,z2,z4,z5,z68]),(0,[z0,z38,z2,z4,z73,z6]),(0,[z49,z0,z181,z4,z5,z6]),(0,[z11,z0,z177,z63,z5,z6]),(0,[z0,z2,z3,z4,z136,z182])],[(0,[z0,z16,z4,z524,z5,z6]),(0,[z231,z165,z0,z3,z104,z6])],[(0,[z0,z2,z3,z4,z5,z184]),(0,[z0,z868,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z869,z6]),(0,[z0,z870,z16,z4,z5,z6]),(0,[z272,z0,z2,z4,z5,z47]),(0,[z0,z74,z3,z62,z5,z6]),(0,[z871,z2,z3,z4,z5,z6]),(0,[z0,z2,z872,z4,z5,z6]),(0,[z275,z308,z0,z2,z5,z43])],[(0,[z0,z2,z873,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z186]),(0,[z0,z385,z2,z4,z5,z6]),(0,[z114,z0,z16,z4,z5,z6]),(0,[z0,z16,z4,z528,z5,z6]),(0,[z0,z2,z874,z4,z5,z6]),(0,[z155,z0,z413,z4,z263,z6]),(0,[z115,z0,z3,z4,z5,z75]),(0,[z109,z0,z56,z4,z5,z6])],[(0,[z49,z58,z17,z4,z5,z6]),(0,[z230,z2,z9,z4,z5,z6]),(0,[z259,z0,z16,z4,z5,z6]),(0,[z49,z798,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z875,z6]),(0,[z165,z0,z876,z4,z5,z6])],[(0,[z0,z462,z16,z4,z5,z6]),(0,[z258,z0,z2,z289,z5,z6]),(0,[z0,z2,z3,z99,z877,z6]),(0,[z0,z878,z2,z4,z5,z6])],[(0,[z575,z0,z16,z4,z5,z6]),(0,[z79,z2,z3,z288,z5,z186]),(0,[z0,z2,z3,z755,z5,z6]),(0,[z0,z56,z4,z318,z5,z6]),(0,[z45,z0,z191,z4,z5,z6]),(0,[z0,z879,z2,z4,z5,z6]),(0,[z0,z2,z3,z92,z5,z195]),(0,[z0,z880,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z881]),(0,[z0,z2,z3,z882,z5,z6]),(0,[z58,z3,z17,z4,z5,z78]),(0,[z0,z883,z2,z3,z4,z5]),(0,[z884,z0,z2,z4,z5,z6]),(0,[z49,z0,z16,z4,z5,z6]),(0,[z0,z885,z3,z4,z5,z6]),(0,[z0,z886,z3,z4,z5,z6]),(0,[z231,z0,z3,z381,z104,z6]),(0,[z231,z0,z2,z335,z104,z6])],[(1,[z0,z736,z4,z5,z6]),(0,[z2,z3,z4,z5,z505,z32]),(0,[z0,z16,z4,z5,z32,z75]),(0,[z0,z215,z16,z4,z12,z6]),(0,[z153,z50,z2,z4,z5,z6]),(0,[z198,z0,z2,z4,z73,z6])],[(0,[z887,z0,z2,z4,z5,z6]),(0,[z0,z16,z4,z289,z5,z6]),(0,[z0,z2,z888,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z889])],[(0,[z0,z395,z2,z4,z5,z6]),(0,[z890,z2,z3,z4,z5,z6]),(0,[z0,z511,z4,z63,z5,z6]),(0,[z0,z2,z3,z4,z5,z891]),(0,[z275,z0,z2,z3,z92,z5])],[(0,[z0,z2,z892,z4,z5,z6]),(0,[z29,z2,z16,z4,z30,z6]),(0,[z0,z48,z3,z4,z12,z6]),(0,[z0,z2,z4,z5,z6,z893]),(0,[z231,z0,z2,z3,z104,z137]),(0,[z0,z2,z3,z4,z5,z894])],[],[(0,[z0,z2,z3,z4,z5,z895]),(0,[z49,z115,z0,z4,z5,z75])]],
   [[(0,[z0,z67,z97,z4,z5,z6]),(0,[z0,z896,z2,z4,z5,z6]),(0,[z155,z0,z3,z4,z263,z6]),(0,[z0,z2,z97,z5,z6,z302])],[(0,[z0,z2,z495,z4,z5,z267]),(0,[z0,z2,z897,z4,z5,z6]),(0,[z0,z2,z3,z5,z783,z43])],[(0,[z0,z383,z2,z4,z5,z6]),(0,[z49,z0,z2,z4,z5,z186]),(0,[z272,z0,z2,z4,z5,z41]),(0,[z49,z512,z2,z4,z5,z6]),(0,[z2,z3,z4,z136,z182,z77])],[(0,[z0,z67,z16,z4,z5,z6]),(0,[z811,z0,z16,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z14]),(0,[z231,z0,z2,z3,z104,z151])],[(0,[z66,z20,z3,z4,z5,z6]),(0,[z0,z829,z3,z4,z5,z6]),(0,[z0,z658,z16,z4,z5,z6]),(0,[z717,z0,z2,z4,z5,z6]),(0,[z898,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z899,z6]),(0,[z900,z0,z2,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z901]),(0,[z0,z2,z16,z4,z5,z78]),(0,[z0,z2,z902,z3,z5,z6]),(0,[z0,z2,z903,z4,z5,z6]),(0,[z0,z227,z16,z63,z5,z6]),(0,[z904,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z905])],[(0,[z82,z3,z17,z4,z5,z6]),(0,[z110,z2,z3,z80,z5,z6]),(0,[z0,z2,z906,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z907]),(0,[z0,z2,z908,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z909,z6]),(0,[z294,z2,z3,z4,z5,z68]),(0,[z65,z49,z0,z4,z5,z6]),(0,[z0,z2,z249,z4,z5,z6]),(0,[z0,z2,z910,z4,z5,z6])],[(0,[z0,z2,z911,z4,z5,z6]),(0,[z176,z2,z361,z4,z5,z6]),(0,[z0,z2,z16,z92,z5,z6]),(0,[z912,z2,z3,z4,z5,z6])],[(0,[z49,z350,z0,z4,z5,z6]),(0,[z2,z3,z4,z391,z5,z32]),(0,[z100,z2,z16,z4,z5,z6]),(0,[z155,z0,z511,z4,z5,z6]),(0,[z0,z913,z3,z4,z5,z6])],[(0,[z58,z495,z17,z4,z5,z6]),(0,[z0,z16,z4,z573,z5,z6]),(0,[z109,z0,z2,z4,z90,z6]),(0,[z165,z3,z4,z5,z24,z6]),(0,[z0,z3,z4,z5,z6,z914])],[(0,[z0,z2,z3,z4,z5,z915]),(0,[z79,z2,z3,z268,z5,z6]),(0,[z0,z3,z4,z5,z916,z6]),(0,[z0,z693,z16,z4,z5,z6]),(0,[z115,z133,z3,z4,z5,z75])],[(0,[z25,z0,z16,z4,z5,z6]),(0,[z193,z549,z2,z4,z5,z6]),(0,[z29,z2,z171,z4,z30,z6]),(0,[z231,z0,z2,z3,z320,z104])],[(0,[z22,z2,z3,z4,z5,z32]),(0,[z0,z265,z3,z4,z5,z6]),(0,[z0,z228,z16,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z267]),(0,[z0,z2,z917,z4,z5,z6]),(0,[z0,z74,z262,z62,z5,z6])]],
   [[(0,[z0,z2,z918,z4,z5,z6]),(0,[z0,z3,z4,z5,z919,z6])],[(0,[z0,z920,z3,z4,z5,z6]),(0,[z0,z16,z4,z5,z582,z6]),(0,[z0,z2,z3,z4,z136,z711])],[(0,[z153,z0,z16,z4,z5,z6]),(1,[z2,z3,z792,z5,z6]),(0,[z0,z2,z921,z4,z5,z6]),(0,[z49,z293,z0,z4,z5,z6]),(0,[z0,z2,z3,z23,z99,z6])],[(0,[z550,z2,z3,z4,z5,z68]),(0,[z0,z883,z2,z16,z4,z5]),(0,[z2,z16,z4,z5,z24,z6]),(0,[z0,z3,z4,z738,z263,z6]),(0,[z922,z0,z3,z4,z5,z6])],[(0,[z0,z2,z923,z4,z5,z6])],[(0,[z29,z2,z3,z4,z626,z6]),(0,[z133,z2,z16,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z924])],[(0,[z66,z58,z16,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z925]),(0,[z0,z2,z16,z4,z5,z137]),(0,[z0,z16,z4,z5,z6,z593]),(0,[z11,z0,z3,z63,z5,z6]),(0,[z0,z2,z3,z4,z5,z926]),(0,[z927,z2,z3,z4,z5,z6]),(0,[z928,z0,z3,z4,z5,z6])],[(0,[z0,z719,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z325]),(0,[z0,z16,z4,z596,z5,z6]),(0,[z0,z2,z4,z5,z6,z929]),(0,[z0,z930,z3,z4,z5,z6])]],
   [[(0,[z931,z0,z2,z3,z4,z5]),(0,[z49,z66,z20,z4,z5,z6]),(0,[z66,z563,z16,z4,z5,z6]),(0,[z2,z16,z4,z5,z6,z77]),(0,[z0,z240,z2,z4,z5,z88]),(0,[z0,z2,z932,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z933]),(0,[z60,z0,z16,z4,z5,z6]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z935,z2,z3,z4,z5,z6])],[(0,[z0,z2,z936,z4,z5,z6]),(0,[z0,z937,z3,z4,z5,z6]),(0,[z110,z383,z2,z80,z5,z6]),(0,[z0,z87,z16,z4,z5,z6]),(0,[z0,z150,z16,z4,z5,z6]),(0,[z49,z155,z0,z4,z263,z6]),(0,[z165,z312,z0,z4,z5,z6])],[(0,[z8,z0,z67,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z938]),(0,[z0,z939,z2,z4,z5,z6]),(0,[z45,z0,z2,z708,z5,z6]),(0,[z0,z2,z4,z5,z335,z6])],[(0,[z58,z0,z16,z4,z5,z267]),(0,[z0,z940,z3,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z151]),(0,[z477,z0,z2,z223,z5,z6]),(0,[z0,z2,z4,z5,z941,z6])],[(0,[z49,z0,z2,z4,z5,z267]),(0,[z0,z832,z3,z4,z5,z6]),(0,[z0,z16,z4,z131,z5,z6]),(0,[z0,z2,z942,z4,z5,z6]),(0,[z308,z0,z2,z4,z5,z6])],[(0,[z0,z943,z3,z4,z5,z6]),(0,[z165,z0,z16,z4,z5,z6]),(0,[z49,z935,z2,z4,z5,z6]),(0,[z94,z0,z2,z3,z92,z195])],[(0,[z825,z0,z383,z4,z5,z6]),(0,[z0,z2,z944,z4,z5,z6]),(0,[z109,z0,z2,z4,z731,z6]),(0,[z103,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z711])]],
   [[(0,[z0,z2,z3,z4,z5,z945]),(0,[z193,z350,z1,z4,z5,z6]),(0,[z0,z946,z2,z4,z5,z6]),(0,[z49,z0,z2,z23,z99,z6]),(0,[z0,z2,z3,z4,z5,z947])],[(0,[z0,z16,z4,z614,z5,z6]),(0,[z0,z16,z4,z615,z5,z6]),(0,[z948,z0,z2,z3,z4,z5]),(0,[z0,z2,z949,z4,z5,z6]),(0,[z950,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z179,z5,z194])],[(0,[z470,z0,z2,z4,z5,z6]),(0,[z312,z0,z2,z4,z5,z6])],[(0,[z0,z16,z4,z621,z5,z6]),(0,[z0,z2,z16,z4,z136,z182]),(0,[z0,z215,z250,z4,z12,z6]),(0,[z512,z385,z2,z4,z5,z6]),(0,[z0,z951,z3,z4,z5,z6])],[(0,[z0,z2,z495,z4,z5,z6]),(0,[z29,z2,z3,z4,z673,z6]),(0,[z218,z0,z3,z63,z5,z6])],[(0,[z0,z2,z16,z4,z5,z184]),(0,[z49,z0,z2,z4,z5,z325]),(0,[z0,z16,z4,z5,z623,z6]),(0,[z529,z0,z16,z4,z5,z6]),(0,[z0,z48,z2,z4,z18,z6]),(0,[z65,z0,z413,z4,z5,z6]),(0,[z0,z74,z511,z4,z5,z6]),(0,[z952,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z5,z877,z6]),(0,[z0,z2,z4,z5,z335,z320])],[(0,[z58,z16,z17,z4,z5,z6]),(0,[z732,z2,z9,z4,z5,z6]),(0,[z0,z16,z4,z625,z5,z6]),(0,[z0,z515,z16,z4,z5,z6]),(0,[z155,z0,z16,z4,z5,z6]),(0,[z264,z0,z215,z4,z12,z6]),(0,[z0,z2,z3,z953,z5,z6]),(0,[z0,z2,z4,z5,z88,z720])],[(0,[z45,z0,z67,z4,z5,z6]),(0,[z0,z191,z16,z4,z5,z6]),(0,[z0,z680,z16,z4,z5,z6])]],
   [[(0,[z954,z2,z3,z4,z5,z6]),(0,[z0,z876,z2,z4,z5,z6])],[(0,[z585,z0,z2,z4,z124,z6]),(0,[z79,z49,z2,z288,z5,z6]),(0,[z0,z2,z3,z89,z92,z5])],[(0,[z829,z3,z17,z4,z5,z6]),(0,[z20,z829,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z718,z75]),(0,[z0,z2,z3,z4,z5,z718]),(0,[z241,z165,z3,z4,z5,z6]),(0,[z0,z2,z3,z23,z877,z6])],[(0,[z732,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z842,z6]),(0,[z0,z2,z3,z4,z5,z955])],[(1,[z0,z832,z4,z5,z6]),(0,[z769,z0,z3,z4,z5,z6]),(0,[z65,z470,z0,z4,z5,z6]),(0,[z312,z0,z2,z4,z5,z320]),(0,[z103,z0,z2,z3,z89,z5])],[(0,[z0,z2,z16,z763,z5,z6])],[(0,[z956,z0,z3,z4,z5,z6]),(0,[z0,z16,z4,z12,z5,z6]),(0,[z0,z2,z3,z89,z5,z783])],[(0,[z0,z3,z16,z4,z5,z78]),(0,[z0,z48,z16,z4,z12,z6]),(0,[z0,z228,z298,z4,z5,z316]),(0,[z0,z2,z4,z5,z720,z41])]],
   [[(0,[z0,z957,z3,z4,z5,z6])],[(1,[z732,z2,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z654]),(0,[z0,z3,z4,z755,z5,z6]),(0,[z0,z958,z2,z4,z5,z6]),(0,[z40,z0,z2,z4,z5,z720]),(0,[z0,z2,z959,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z780]),(0,[z0,z135,z16,z4,z5,z6]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z207,z191,z3,z4,z5,z6])],[(0,[z45,z0,z2,z173,z5,z6]),(0,[z551,z2,z3,z4,z5,z32]),(0,[z0,z229,z16,z4,z5,z6]),(0,[z2,z3,z4,z5,z785,z6]),(0,[z103,z2,z3,z4,z5,z24])],[(0,[z0,z2,z3,z4,z5,z961]),(0,[z49,z207,z2,z4,z5,z6]),(0,[z0,z3,z4,z12,z102,z6]),(0,[z0,z962,z3,z4,z5,z6])],[(0,[z0,z200,z16,z4,z5,z6]),(0,[z0,z1,z534,z4,z5,z6]),(0,[z79,z2,z3,z288,z5,z6]),(0,[z0,z239,z4,z5,z6,z75])],[(0,[z0,z2,z3,z4,z5,z963]),(0,[z0,z964,z3,z4,z5,z6]),(0,[z0,z53,z16,z4,z5,z6]),(0,[z0,z56,z16,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z675]),(0,[z49,z0,z191,z4,z5,z6]),(0,[z155,z0,z3,z4,z33,z6]),(0,[z965,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z966,z6])],[(0,[z0,z2,z967,z4,z5,z6]),(0,[z968,z0,z16,z4,z5,z6]),(0,[z241,z312,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z969,z4,z5,z6]),(0,[z0,z2,z970,z4,z5,z6]),(0,[z49,z22,z2,z4,z5,z32]),(0,[z152,z2,z3,z4,z5,z32]),(0,[z272,z0,z16,z4,z5,z75])],[(0,[z0,z16,z4,z5,z68,z75]),(0,[z971,z2,z3,z4,z5,z6]),(0,[z0,z2,z972,z4,z5,z6])],[(0,[z329,z0,z16,z4,z5,z6]),(0,[z0,z57,z16,z4,z5,z6]),(1,[z0,z3,z755,z5,z6]),(0,[z0,z973,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z974]),(0,[z0,z870,z2,z4,z5,z6]),(0,[z49,z0,z497,z4,z5,z6]),(0,[z0,z975,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z320])],[(0,[z233,z2,z3,z4,z5,z32]),(0,[z976,z0,z2,z3,z5,z6]),(0,[z977,z0,z2,z4,z5,z6]),(0,[z11,z0,z3,z755,z5,z6]),(0,[z0,z2,z3,z4,z738,z6]),(0,[z0,z2,z3,z4,z5,z978])],[(0,[z0,z2,z3,z4,z5,z979]),(0,[z0,z980,z2,z4,z5,z6]),(0,[z8,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z792,z5,z6]),(0,[z2,z3,z4,z792,z5,z6]),(0,[z0,z981,z2,z4,z5,z6]),(0,[z292,z191,z3,z4,z5,z6])],[(0,[z58,z0,z16,z4,z5,z6]),(0,[z193,z0,z67,z4,z5,z6]),(0,[z0,z2,z982,z4,z5,z6])]],
   [[(0,[z49,z0,z2,z4,z5,z6]),(0,[z0,z2,z826,z4,z5,z6])],[(0,[z0,z2,z983,z4,z5,z6]),(0,[z0,z74,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z984]),(0,[z0,z985,z3,z4,z5,z6])],[(0,[z0,z2,z986,z4,z5,z6]),(0,[z0,z2,z3,z987,z5,z6]),(0,[z0,z2,z988,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z42]),(0,[z989,z2,z3,z4,z5,z6])],[(0,[z0,z2,z990,z4,z5,z6]),(0,[z0,z228,z3,z4,z5,z202]),(0,[z0,z3,z4,z5,z738,z6]),(0,[z231,z2,z3,z24,z104,z6])],[(0,[z155,z0,z870,z4,z5,z6]),(0,[z0,z3,z4,z5,z381,z6]),(0,[z0,z2,z3,z4,z138,z182])],[(0,[z0,z2,z16,z4,z5,z122]),(0,[z0,z2,z3,z991,z5,z6]),(1,[z0,z2,z4,z5,z720]),(0,[z0,z2,z3,z4,z5,z720]),(0,[z94,z0,z2,z3,z4,z340])],[(0,[z0,z2,z3,z4,z5,z992]),(0,[z0,z2,z993,z4,z5,z6])],[(0,[z0,z994,z2,z4,z5,z6]),(0,[z717,z0,z3,z4,z5,z6]),(0,[z553,z0,z16,z4,z5,z6]),(0,[z862,z0,z2,z16,z4,z5]),(0,[z0,z995,z3,z4,z5,z6]),(0,[z412,z0,z2,z3,z4,z195])]],
   [[(0,[z94,z0,z2,z3,z4,z277]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z0,z997,z3,z4,z5,z6]),(0,[z40,z0,z265,z4,z5,z41])],[(1,[z0,z16,z4,z5,z78]),(0,[z0,z2,z3,z998,z5,z6])],[(0,[z49,z0,z2,z4,z5,z320])],[(0,[z66,z539,z20,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z999]),(0,[z811,z0,z2,z4,z5,z6]),(0,[z231,z0,z2,z3,z104,z6]),(0,[z306,z0,z2,z3,z5,z43]),(0,[z0,z2,z3,z89,z5,z194])],[(0,[z0,z2,z3,z4,z5,z1000]),(0,[z0,z2,z3,z1001,z5,z6]),(0,[z0,z139,z16,z4,z5,z6]),(0,[z0,z591,z16,z4,z5,z6]),(0,[z0,z2,z3,z1002,z5,z6])],[(0,[z58,z0,z158,z4,z5,z6]),(0,[z49,z292,z2,z4,z5,z6]),(0,[z1003,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1004]),(0,[z0,z2,z262,z4,z5,z6]),(0,[z40,z0,z2,z4,z5,z86]),(0,[z0,z2,z3,z4,z5,z1005]),(0,[z312,z0,z4,z5,z381,z6]),(0,[z0,z3,z4,z5,z381,z320])],[(0,[z0,z1006,z2,z4,z5,z6]),(0,[z241,z2,z4,z5,z335,z6])]],
   [[(0,[z968,z0,z228,z4,z5,z6]),(0,[z155,z0,z250,z4,z5,z6]),(0,[z133,z2,z3,z4,z5,z316]),(0,[z0,z4,z5,z335,z381,z6]),(0,[z1007,z2,z3,z4,z5,z6]),(0,[z0,z2,z1008,z4,z5,z6])],[(0,[z8,z50,z2,z4,z5,z6]),(0,[z29,z2,z3,z4,z5,z122]),(0,[z0,z16,z4,z5,z6,z290]),(0,[z0,z2,z3,z4,z5,z783])],[(0,[z2,z3,z17,z4,z5,z78]),(0,[z110,z2,z111,z80,z5,z6]),(0,[z2,z3,z4,z842,z30,z6]),(0,[z566,z0,z16,z4,z5,z6]),(0,[z0,z157,z16,z4,z5,z6])],[(0,[z1009,z0,z2,z4,z5,z6]),(0,[z1010,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z782,z6])],[(0,[z0,z2,z1011,z4,z5,z6]),(0,[z100,z2,z3,z4,z136,z182])],[(0,[z539,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z92,z5,z68]),(0,[z1012,z0,z2,z4,z5,z6]),(0,[z0,z1013,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z194,z77])],[(0,[z0,z2,z3,z4,z5,z1014]),(0,[z1015,z0,z2,z4,z5,z6]),(0,[z0,z228,z16,z4,z5,z75]),(0,[z805,z2,z3,z4,z5,z6]),(0,[z155,z0,z3,z4,z156,z6]),(0,[z0,z1016,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1017]),(0,[z0,z2,z4,z5,z6,z1018])],[(0,[z40,z0,z2,z4,z5,z232])]],
   [[(0,[z0,z2,z1019,z4,z5,z6]),(0,[z0,z1020,z3,z4,z5,z6]),(0,[z533,z0,z16,z4,z5,z6]),(0,[z49,z133,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1021]),(0,[z0,z2,z3,z1022,z5,z6]),(0,[z49,z0,z2,z89,z5,z194]),(0,[z0,z2,z3,z4,z877,z6])],[(0,[z0,z1023,z2,z4,z5,z6]),(0,[z29,z2,z236,z4,z30,z6]),(0,[z0,z168,z16,z4,z5,z6]),(0,[z231,z0,z2,z3,z877,z6]),(0,[z778,z0,z2,z4,z5,z6])],[(0,[z0,z395,z2,z4,z5,z78]),(0,[z0,z2,z1024,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1025])],[(0,[z1026,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z5,z6]),(0,[z103,z0,z2,z4,z5,z335]),(0,[z1027,z0,z2,z4,z5,z6]),(0,[z0,z2,z888,z92,z5,z6])],[(0,[z193,z1,z2,z4,z5,z6]),(0,[z0,z732,z2,z4,z5,z6]),(0,[z0,z38,z67,z4,z5,z6]),(0,[z0,z2,z1028,z4,z5,z6]),(0,[z45,z0,z56,z318,z5,z6]),(0,[z103,z312,z0,z2,z4,z5]),(0,[z0,z2,z3,z5,z6,z783])],[(0,[z0,z2,z1029,z4,z5,z6]),(0,[z1030,z2,z3,z4,z5,z6]),(0,[z0,z38,z2,z4,z18,z6]),(0,[z1031,z0,z2,z4,z5,z6])],[(0,[z0,z1,z56,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1032]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z1033,z3,z4,z5,z6]),(0,[z0,z2,z1034,z4,z5,z6])]],
   [[(0,[z0,z16,z4,z128,z5,z6]),(0,[z0,z16,z4,z129,z5,z6]),(0,[z0,z2,z3,z5,z823,z6]),(0,[z103,z0,z2,z3,z5,z43]),(0,[z94,z2,z3,z4,z5,z77])],[(0,[z512,z2,z3,z4,z5,z6]),(0,[z0,z1035,z3,z4,z5,z6]),(0,[z0,z2,z1036,z4,z5,z6]),(0,[z1037,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1038]),(0,[z0,z2,z3,z4,z136,z540]),(0,[z0,z2,z3,z92,z5,z182])],[(0,[z0,z2,z1039,z4,z5,z6]),(0,[z2,z3,z4,z5,z1040,z6]),(0,[z133,z385,z2,z4,z5,z6])],[(0,[z578,z0,z16,z4,z5,z6]),(0,[z0,z534,z9,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z195])],[(0,[z66,z829,z3,z4,z5,z6]),(0,[z0,z216,z16,z4,z5,z6]),(0,[z0,z2,z902,z16,z5,z6]),(0,[z0,z2,z4,z731,z124,z6])],[(0,[z49,z0,z545,z4,z5,z6]),(0,[z0,z2,z3,z23,z169,z6])],[(0,[z0,z2,z3,z4,z1041,z6]),(0,[z49,z0,z67,z4,z5,z6]),(0,[z241,z2,z3,z4,z5,z6]),(0,[z1042,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1043]),(0,[z0,z2,z4,z5,z6,z1044]),(0,[z281,z0,z2,z3,z5,z43])],[(0,[z79,z2,z16,z288,z5,z6]),(0,[z0,z2,z4,z5,z6,z1045]),(0,[z119,z0,z191,z4,z5,z6])]],
   [[(0,[z0,z74,z16,z62,z5,z6]),(0,[z218,z0,z2,z318,z5,z6])],[(0,[z0,z2,z1046,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z186]),(0,[z450,z0,z2,z3,z5,z43]),(0,[z115,z0,z16,z4,z5,z75]),(0,[z977,z0,z4,z5,z381,z6]),(0,[z0,z2,z4,z5,z6,z1047]),(0,[z1048,z0,z2,z4,z5,z6])],[(0,[z0,z2,z1049,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z840]),(0,[z49,z0,z2,z13,z5,z6]),(0,[z0,z1050,z2,z4,z5,z6]),(0,[z292,z40,z2,z4,z5,z41]),(0,[z0,z61,z191,z4,z5,z6]),(0,[z165,z0,z872,z4,z5,z6]),(0,[z0,z2,z3,z5,z194,z783])],[(0,[z801,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1051]),(0,[z0,z3,z755,z63,z5,z6]),(0,[z1052,z2,z3,z4,z5,z6]),(0,[z0,z228,z239,z4,z5,z6]),(0,[z0,z2,z3,z4,z1053,z6])],[(0,[z0,z2,z1054,z4,z5,z6]),(0,[z1055,z0,z2,z4,z5,z6]),(0,[z576,z0,z2,z4,z5,z86]),(0,[z49,z0,z4,z5,z381,z6]),(0,[z412,z0,z2,z3,z104,z6])],[(0,[z0,z2,z1056,z4,z5,z6]),(0,[z0,z1057,z3,z4,z5,z6]),(0,[z0,z2,z3,z1058,z5,z6]),(0,[z0,z16,z4,z5,z6,z172]),(0,[z555,z0,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1059]),(1,[z0,z3,z4,z5,z718])],[(0,[z453,z0,z16,z4,z5,z6]),(0,[z0,z16,z4,z174,z5,z6]),(0,[z0,z2,z16,z4,z5,z320]),(0,[z308,z0,z826,z4,z5,z6])],[(0,[z810,z0,z2,z3,z5,z6]),(0,[z0,z2,z1060,z4,z5,z6]),(0,[z11,z0,z511,z63,z5,z6]),(0,[z221,z0,z74,z62,z5,z6]),(0,[z1061,z2,z3,z4,z5,z6]),(0,[z231,z103,z0,z2,z3,z104]),(0,[z2,z3,z4,z5,z77,z43])]],
   [[(0,[z58,z829,z3,z4,z5,z6]),(0,[z66,z176,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1062]),(0,[z2,z3,z4,z5,z6,z1063]),(0,[z241,z2,z3,z4,z5,z320]),(0,[z103,z0,z3,z4,z5,z381])],[(0,[z119,z0,z2,z4,z5,z430])],[(0,[z0,z2,z158,z4,z5,z6]),(0,[z220,z1,z2,z4,z5,z6]),(0,[z0,z1064,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1065]),(0,[z0,z2,z1066,z4,z5,z6]),(0,[z133,z2,z239,z4,z5,z6])],[(0,[z0,z1067,z2,z4,z5,z6]),(0,[z1068,z0,z2,z4,z5,z6])],[(0,[z0,z1069,z2,z4,z5,z6]),(0,[z0,z2,z1070,z4,z5,z6]),(0,[z0,z1071,z3,z4,z5,z6]),(0,[z29,z2,z3,z4,z5,z184]),(0,[z0,z413,z2,z4,z5,z6]),(0,[z0,z16,z4,z73,z5,z6]),(0,[z259,z0,z413,z4,z5,z6]),(0,[z0,z2,z3,z877,z104,z6])],[(0,[z149,z1,z2,z4,z5,z6]),(0,[z0,z1072,z3,z4,z5,z6]),(0,[z155,z0,z16,z4,z263,z6]),(0,[z49,z728,z2,z4,z5,z6]),(0,[z0,z2,z1073,z4,z5,z6]),(0,[z0,z2,z3,z4,z711,z195])],[(0,[z66,z0,z16,z4,z5,z6]),(0,[z58,z3,z17,z4,z5,z267]),(0,[z0,z454,z16,z4,z5,z6]),(0,[z0,z736,z3,z4,z5,z6]),(0,[z931,z0,z2,z16,z4,z5]),(0,[z259,z0,z38,z4,z18,z6])],[(0,[z0,z2,z3,z4,z5,z1074]),(0,[z0,z2,z1075,z4,z5,z6])]],
   [[(0,[z0,z2,z1076,z4,z5,z6]),(0,[z193,z563,z2,z4,z5,z6]),(0,[z0,z390,z16,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z86])],[(0,[z66,z20,z16,z4,z5,z6]),(0,[z0,z56,z9,z4,z5,z6]),(0,[z1077,z0,z2,z4,z5,z6]),(0,[z0,z2,z1078,z4,z5,z6]),(0,[z0,z2,z1079,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1080]),(0,[z996,z2,z16,z4,z5,z6]),(0,[z0,z2,z4,z5,z88,z359]),(0,[z0,z2,z3,z1081,z5,z6]),(0,[z0,z2,z1082,z4,z5,z6])],[(0,[z643,z0,z16,z4,z5,z6]),(0,[z1083,z0,z2,z4,z5,z6]),(0,[z0,z522,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z867]),(0,[z492,z0,z534,z4,z5,z6])],[(0,[z110,z2,z16,z80,z5,z6]),(0,[z65,z221,z0,z4,z5,z6])],[(0,[z58,z395,z17,z4,z5,z6]),(0,[z0,z2,z111,z4,z5,z6]),(0,[z21,z2,z171,z4,z5,z6]),(0,[z1084,z0,z2,z4,z5,z6]),(0,[z103,z0,z2,z16,z4,z5]),(0,[z0,z2,z96,z223,z5,z6]),(0,[z0,z3,z4,z5,z316,z718]),(0,[z0,z534,z4,z18,z5,z6])],[(0,[z1085,z0,z3,z4,z5,z6]),(0,[z0,z81,z16,z4,z5,z6]),(0,[z912,z2,z16,z4,z5,z6]),(0,[z94,z0,z2,z16,z4,z195]),(0,[z221,z0,z16,z4,z5,z6]),(0,[z49,z2,z4,z5,z6,z77])],[(0,[z0,z2,z1086,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1087]),(0,[z968,z0,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z1088,z6])]],
   [[(0,[z1089,z0,z2,z3,z4,z5]),(0,[z259,z0,z3,z4,z5,z6]),(1,[z0,z3,z4,z738,z6]),(0,[z512,z115,z3,z4,z5,z75])],[(0,[z0,z2,z4,z5,z6,z1090]),(0,[z0,z2,z3,z5,z340,z43])],[(0,[z0,z2,z3,z4,z5,z1091]),(0,[z2,z3,z4,z31,z5,z122]),(0,[z275,z0,z2,z3,z5,z43]),(1,[z0,z2,z3,z5,z783])],[(0,[z193,z1,z67,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1092]),(0,[z79,z2,z3,z792,z5,z6]),(0,[z22,z2,z16,z4,z5,z32]),(0,[z0,z265,z16,z4,z5,z6]),(0,[z115,z0,z239,z4,z5,z75]),(1,[z0,z826,z4,z5,z6])],[(0,[z0,z2,z16,z4,z5,z267]),(0,[z66,z0,z158,z4,z5,z6]),(0,[z1093,z0,z2,z4,z5,z6]),(0,[z0,z215,z3,z4,z12,z6]),(0,[z1094,z2,z3,z4,z5,z6])],[(0,[z66,z519,z3,z4,z5,z6]),(0,[z1095,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1096])],[(0,[z0,z16,z4,z5,z6,z246]),(0,[z0,z3,z62,z5,z279,z6])],[(0,[z0,z2,z1097,z4,z5,z6]),(0,[z66,z20,z158,z4,z5,z6]),(0,[z0,z2,z16,z23,z99,z6]),(0,[z0,z2,z708,z318,z5,z6]),(0,[z0,z61,z2,z4,z5,z720])]],
   [[(0,[z2,z3,z792,z288,z5,z6]),(0,[z1098,z0,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1099]),(0,[z0,z2,z96,z97,z5,z6]),(0,[z0,z1100,z3,z4,z5,z6]),(0,[z0,z2,z97,z5,z613,z6])],[(0,[z350,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1101]),(0,[z0,z326,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z1102,z6]),(0,[z231,z312,z0,z2,z104,z6]),(0,[z0,z2,z3,z4,z5,z1103])],[(0,[z55,z2,z3,z4,z5,z68]),(0,[z0,z2,z1104,z4,z5,z6]),(1,[z0,z2,z3,z877,z6])],[(0,[z2,z3,z4,z5,z6,z77]),(0,[z0,z16,z4,z5,z255,z6]),(0,[z11,z0,z16,z63,z5,z6]),(0,[z0,z2,z511,z4,z5,z6]),(0,[z0,z2,z3,z5,z104,z151])],[(0,[z0,z702,z16,z4,z5,z6]),(0,[z0,z2,z16,z4,z5,z325]),(0,[z0,z240,z16,z4,z5,z75]),(0,[z0,z16,z4,z5,z260,z6]),(0,[z1105,z0,z2,z4,z5,z6]),(0,[z0,z228,z3,z4,z5,z316])],[(0,[z0,z2,z3,z4,z1106,z6]),(0,[z0,z16,z4,z261,z5,z6]),(0,[z0,z2,z1107,z4,z5,z6])],[(0,[z374,z2,z3,z4,z5,z32]),(0,[z0,z423,z16,z4,z5,z6]),(0,[z1108,z0,z2,z4,z5,z6]),(0,[z1109,z2,z3,z4,z5,z6]),(0,[z207,z265,z3,z4,z5,z6]),(0,[z0,z2,z1110,z4,z5,z6]),(0,[z0,z2,z4,z5,z1111,z6])],[(0,[z0,z1112,z2,z4,z5,z6]),(0,[z49,z0,z461,z4,z5,z6]),(0,[z0,z2,z3,z4,z136,z372]),(0,[z21,z2,z3,z4,z5,z737]),(0,[z0,z72,z16,z4,z5,z6]),(0,[z264,z0,z2,z4,z5,z6]),(0,[z1113,z2,z3,z4,z5,z6]),(1,[z0,z2,z708,z5,z6]),(0,[z0,z2,z3,z708,z5,z6])]],
   [[(0,[z0,z2,z1114,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z75]),(0,[z49,z0,z534,z4,z5,z6]),(0,[z1115,z0,z2,z3,z4,z6]),(0,[z2,z3,z4,z5,z24,z320])],[(0,[z0,z2,z3,z4,z5,z78]),(0,[z2,z171,z4,z5,z6,z32]),(0,[z21,z2,z3,z4,z5,z300]),(0,[z0,z16,z4,z5,z279,z6]),(0,[z0,z2,z3,z4,z6,z1116]),(0,[z0,z74,z3,z755,z5,z6]),(0,[z0,z228,z3,z4,z5,z718])],[(0,[z0,z2,z3,z4,z5,z1117]),(0,[z197,z0,z2,z4,z332,z6]),(0,[z1118,z2,z3,z4,z5,z6]),(0,[z2,z4,z5,z335,z24,z6]),(0,[z165,z0,z4,z5,z335,z6])],[(0,[z0,z2,z1119,z4,z5,z6]),(0,[z2,z3,z4,z5,z737,z6]),(0,[z0,z346,z16,z4,z5,z6]),(0,[z0,z511,z4,z12,z5,z6]),(0,[z0,z2,z3,z4,z5,z1120]),(0,[z0,z56,z4,z18,z5,z6]),(0,[z1121,z0,z2,z4,z5,z6])],[(0,[z1122,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z92,z5,z6]),(0,[z0,z2,z3,z4,z182,z711])],[(0,[z0,z1123,z2,z4,z5,z6]),(0,[z65,z717,z0,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1124])],[(0,[z308,z0,z813,z4,z5,z6])],[(0,[z1125,z0,z2,z3,z5,z6]),(0,[z0,z16,z4,z63,z5,z6]),(0,[z209,z0,z16,z4,z5,z6]),(0,[z115,z0,z385,z4,z5,z75]),(0,[z0,z2,z1126,z4,z5,z6])]],
   [[(0,[z49,z0,z341,z4,z5,z6]),(0,[z40,z0,z56,z4,z5,z6]),(0,[z103,z241,z2,z3,z4,z5])],[(0,[z58,z3,z17,z4,z5,z6]),(0,[z218,z0,z16,z63,z5,z6]),(0,[z0,z38,z2,z4,z731,z6]),(0,[z40,z207,z2,z4,z5,z41]),(0,[z0,z2,z3,z89,z5,z339])],[(0,[z0,z1127,z3,z4,z5,z6]),(0,[z2,z3,z4,z31,z214,z6]),(0,[z0,z370,z16,z4,z5,z6]),(0,[z0,z2,z1128,z4,z5,z6]),(0,[z292,z265,z3,z4,z5,z6])],[(0,[z0,z2,z1129,z4,z5,z6]),(0,[z0,z2,z1130,z4,z5,z6]),(0,[z1131,z0,z2,z4,z5,z6]),(0,[z976,z0,z2,z16,z5,z6])],[(0,[z21,z2,z3,z4,z5,z690]),(0,[z0,z1132,z2,z4,z5,z6])],[(0,[z1133,z0,z2,z4,z5,z6]),(0,[z1134,z0,z2,z4,z5,z6]),(1,[z2,z3,z4,z5,z737]),(0,[z0,z16,z4,z310,z5,z6]),(0,[z275,z0,z2,z16,z5,z43]),(0,[z0,z521,z16,z4,z5,z6]),(0,[z241,z49,z2,z4,z5,z6]),(0,[z0,z1135,z3,z4,z5,z6]),(0,[z1136,z0,z2,z4,z5,z6])],[(0,[z58,z0,z16,z4,z5,z78]),(0,[z448,z1,z2,z4,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z0,z1138,z3,z4,z5,z6]),(0,[z312,z2,z4,z5,z24,z6])],[(0,[z49,z0,z2,z4,z5,z78]),(0,[z1139,z0,z3,z4,z5,z6]),(0,[z0,z16,z4,z5,z6,z315]),(0,[z0,z16,z4,z317,z5,z6]),(0,[z1140,z2,z3,z4,z5,z6])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1049).take 154) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1203)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 521, 154] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 106).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 222).take 34).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [106, 116, 34] = true :=
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

end PEqualNP.Outside.L_meta_45782

theorem PEqualNP.Outside.L_meta_45782 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4008232960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4008232960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45782.solve