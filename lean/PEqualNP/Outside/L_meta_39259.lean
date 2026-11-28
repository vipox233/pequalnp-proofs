import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39259

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
  Nat.testBit (4277074632 * 2 ^ 32 + 4276680904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010d0e206358c64#64 ++ 0xb40043438818d631#64 ++ 0x80b1d3e60e7d9cfd#64 ++ 0xfa02c74f9839f673#64 : BitVec 256),
   (0x0106220c308a1188#64 ++ 0x0804188830c22846#64 ++ 0xb34e223e718e1ffb#64 ++ 0xf6cd3888f9c6387f#64 : BitVec 256),
   (0x047014308150a630#64 ++ 0x1011c050c2054298#64 ++ 0xcc703c3981f3e737#64 ++ 0xaf31c0f0e607cf9c#64 : BitVec 256),
   (0x0b802b415a035801#64 ++ 0x202e00ad05680d60#64 ++ 0xdf803fc1fe03f82f#64 ++ 0x9f7e00ff07f80fe0#64 : BitVec 256),
   (0x1eeb4001edec0001#64 ++ 0xc07bad0007b7b000#64 ++ 0xffffc001fffc001f#64 ++ 0x7fffff0007fff000#64 : BitVec 256),
   (0x2ffdbfbe0000003e#64 ++ 0x00bff6fef8000000#64 ++ 0xaffffffe00000000#64 ++ 0xfebffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3e60e7d9cfd 0xfa02c74f9839f673

def z1 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e223e718e1ffb 0xf6cd3888f9c6387f

def z2 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c3981f3e737 0xaf31c0f0e607cf9c

def z3 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc1fe03f82f 0x9f7e00ff07f80fe0

def z4 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fffc001f 0x7fffff0007fff000

def z5 : W := mkw 0x247994b200000036 0x0091e652c8000000 0x0031c00000000000 0x0000c70000000000

def z6 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00000000 0xfebffffff8000000

def z7 : W := mkw 0x1b8b6b417eaf5801 0xe06e2dad05fabd60 0xff8fffc1fe0ff82f 0xdffe3fff07f83fe0

def z8 : W := mkw 0x000000008150a600 0x1000000002054298 0x4000000181f3e737 0x010000000607cf9c

def z9 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x238fc3c600000000 0x508e3f0f18000000

def z10 : W := mkw 0x1fef620dfdee1189 0xc87fbd8837f7b846 0xffffe019fffe031f 0x7fffff8067fff80c

def z11 : W := mkw 0x2fed2f1c0000001a 0x00bfb4bc70000000 0xafce3fd800000000 0x9ebf38ff60000000

def z12 : W := mkw 0x001090e202118c64 0x3400424388084631 0x000013e600019ce0 0x8000004f98000673

def z13 : W := mkw 0x1eeb0001e9c80001 0x407bac0007a72000 0x7f4e0001f1800002 0x05fd380007c60000

def z14 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa3cfe3fe00000000 0xf68f3f8ff8000000

def z15 : W := mkw 0x0002000020880000 0x0000080000822000 0xb34e0000718c001b 0x76cd380001c63000

def z16 : W := mkw 0x1fef620dfdee1189 0xc87fbd8837f7b846 0xffffe23ffffe1fff 0xffffff88fffff87f

def z17 : W := mkw 0x0b802b41db53fe01 0x302e00ad076d4ff8 0xdf803fc1fff3ff3f 0x9f7e00ff07ffcffc

def z18 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x9f803fc07e001808 0x9e7e00ff01f80060

def z19 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2ffffdd800000000 0x0cbffff760000000

def z20 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x0081c3c60e0c18c8 0x5002070f18383063

def z21 : W := mkw 0x0104220c10021188 0x0804108830400846 0x0000223e00021fe0 0x80000088f800087f

def z22 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0xafffddc000000000 0x7ebfff7700000000

def z23 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81f3e737 0xffbffffffe07cf9c

def z24 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0x2fcfefde00000000 0x54bf3fbf78000000

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001820733 0x000000000006081c

def z26 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x138003c07e001808 0x104e000f01f80060

def z27 : W := mkw 0x0b862b4d7a8b5989 0x282e18ad35ea2d66 0xffce3fffff8fffff 0xffff38fffffe3fff

def z28 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x0070003801f00710 0x2001c000e007c01c

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000226000c1cf9 0xf200000898003073

def z30 : W := mkw 0x0116f2ee36bf9dec 0xbc045bcbb8dafe77 0xb3fff3fe7fff9fff 0xfecfffcff9fffe7f

def z31 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c002c0180026002 0x053000b006000980

def z32 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0xccb1ffe78e7ffcff 0xff32c7ff9e39fff3

def z33 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xfffffc01ffffe03f 0xfffffff007ffff80

def z34 : W := mkw 0x1feb6b41ffef5801 0xe07fadad07ffbd60 0xffffffc1fffff83f 0xffffffff07ffffe0

def z35 : W := mkw 0x046000008150a600 0x1011800002054298 0xcc70000181f3e737 0x2f31c0000607cf9c

def z36 : W := mkw 0x1efbd0a3edfc8465 0xd47bef428fb7f211 0xffffc027fffc04df 0x7fffff009ffff013

def z37 : W := mkw 0x2fed2f1c0000001a 0x00bfb4bc70000000 0x2f4e2c1800000000 0x04bd38b060000000

def z38 : W := mkw 0x2ffdfffe06358c7e 0xb4bff7fff818d631 0xaffffffe0e7d9cfd 0xfebffffff839f673

def z39 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x330e0206700c18c8 0x50cc380819c03063

def z40 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c301c018071e004 0x0930c0700601c780

def z41 : W := mkw 0x00020000308a1180 0x0800080000c22846 0x10000000718e1ffb 0x0040000001c6387f

def z42 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0x0cb1ddc000000000 0x0832c77700000000

def z43 : W := mkw 0x0ee9000081400000 0x003ba40002050000 0xefffc00181f00017 0x7fbfff000607c000

def z44 : W := mkw 0x000000415a035801 0x2000000105680d60 0x50000001fe03f82f 0x0140000007f80fe0

def z45 : W := mkw 0x10024001edec0001 0xc040090007b7b000 0x50000001fffc001f 0x0140000007fff000

def z46 : W := mkw 0x000000008150a600 0x1000000002054298 0xcc003c0181f3e737 0x8f3000f00607cf9c

def z47 : W := mkw 0x0006000c20880188 0x0800180030822006 0x204e003e018c07d0 0x60813800f806301f

def z48 : W := mkw 0x0a8009414a014801 0x202a002505280520 0x4c801dc18e01e004 0x0932007706380780

def z49 : W := mkw 0x0000404006358c40 0xb40001010018d631 0x800002260e7d9cfd 0xf20000089839f673

def z50 : W := mkw 0x0010102000108420 0x1000404080004210 0x8030102000718435 0xaa00c0408001c610

def z51 : W := mkw 0x0470d4f28775ae74 0xb411c353ca1dd6b9 0xccf1ffff8fffffff 0xff33c7fffe3fffff

def z52 : W := mkw 0x0b80ebc35e275845 0xa42e03af0d789d61 0xdf81ffc7fe0ff8ef 0xdf7e07ff1ff83fe3

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc403c398183e737 0xaf3100f0e6060f9c

def z54 : W := mkw 0x0000094002014800 0x2000002500080520 0x00001dc00001e000 0x0000007700000780

def z55 : W := mkw 0x3fffffbffdee11bf 0xc8fffffefff7b846 0xfffffffffffe1fff 0xfffffffffffff87f

def z56 : W := mkw 0x0110fbe21637dc64 0xb40443ef8858df71 0x80b1ffe60e7ffcfd 0xfa02c7ff9839fff3

def z57 : W := mkw 0x0460041081402210 0x0011801042050088 0xcc403c198183e327 0x8f3100f066060f8c

def z58 : W := mkw 0x0000400004240000 0x8000010000109000 0x80b1c0000e7c001d 0x7a02c7000039f000

def z59 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xaffffffe01f00710 0xfebffffff807c01c

def z60 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f803dc1fe03e006 0x0d7e00f707f80f80

def z61 : W := mkw 0x1eeb0001e9c80001 0x407bac0007a72000 0xffffc001f1800002 0x7fffff0007c60000

def z62 : W := mkw 0x0000000010021000 0x0000000000400840 0x100000007002182b 0x0040000001c00860

def z63 : W := mkw 0x0574363c9152b7b8 0x1815d0d8f2454ade 0xcc703e3f81f3fff7 0xaf31c0f8fe07cfff

def z64 : W := mkw 0x1ee94001cd640001 0xc07ba50007359000 0x4cb1c0018e700004 0x0932c7000639c000

def z65 : W := mkw 0x0b842b4d5a035809 0x202e10ad35680d60 0xffce3ffffe03f82f 0xffff38fffff80fe0

def z66 : W := mkw 0x1efb5431edfca631 0xd07bed50c7b7f298 0xfffffc39ffffe73f 0xfffffff0e7ffff9c

def z67 : W := mkw 0x2ffdbfbe0010a63e 0x10bff6fef8004298 0xaffffffe0003e720 0xfebffffff8000f9c

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000022600001ce0 0x8000000898000073

def z69 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e223e700c18c8 0xf6cd3888f9c03063

def z70 : W := mkw 0x14624001edec0001 0xc051890007b7b000 0xdc700001fffc001f 0x2f71c00007fff000

def z71 : W := mkw 0x0b802b0000000000 0x002e00ac00000000 0x8f803fc000000000 0x9e3e00ff00000000

def z72 : W := mkw 0x2ffdbfff5a03583f 0x20bff6fffd680d60 0xfffffffffe03f82f 0xfffffffffff80fe0

def z73 : W := mkw 0x0fef220c308a1188 0x083fbc8830c22846 0xbfffe23e718e1ffb 0xfeffff88f9c6387f

def z74 : W := mkw 0x046004108150a610 0x1011801042054298 0x4c402c1981f3e737 0x053100b06607cf9c

def z75 : W := mkw 0x2ef9ddf206358c76 0xb4bbe777c818d631 0x0cb1ddc00e718004 0x0832c7770039c600

def z76 : W := mkw 0x1fe96b41df675801 0xe07fa5ad077d9d60 0xdfb1ffc1fe73f82f 0x9f7ec7ff07f9cfe0

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc003c018003e027 0x8f3000f006000f80

def z78 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1c3e60e7c1cd8 0x7002c70f9839f073

def z79 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c703c1981f3e306 0x0d31c0f06607cf8c

def z80 : W := mkw 0x1efbd0e3effd8c65 0xf47bef438fbff631 0xffffd3e7fffd9cff 0xffffff4f9ffff673

def z81 : W := mkw 0x2fffbfff7a8b59bf 0x28bffefffdea2d66 0xffffffffff8fffff 0xfffffffffffe3fff

def z82 : W := mkw 0x000000414a014801 0x2000000105280520 0x400000018e01e004 0x0100000006380780

def z83 : W := mkw 0x2ffdbfbe100211be 0x08bff6fef8400846 0xaffffffe00021fe0 0xfebffffff800087f

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003c000003e020 0x800000f000000f80

def z85 : W := mkw 0x001014300010a630 0x10004050c0004298 0x00003c380003e720 0x800000f0e0000f9c

def z86 : W := mkw 0x2fedab8e0000000e 0x00bfb6ae38000000 0xafffc3c600000000 0x7ebfff0f18000000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000026000c04d0 0x6000000098003013

def z88 : W := mkw 0x0116b2ae308a11ac 0x08045acab8c22846 0xb3fff3fe718e1ffb 0xfecfffcff9c6387f

def z89 : W := mkw 0x0b802b0158025001 0x002e00ac05600940 0xdf803fc1f0026002 0x9f7e00ff07c00980

def z90 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fbfc001fe7c000c 0x59feff0007f9f000

def z91 : W := mkw 0x0104220c00000008 0x0004108830000000 0xa34e223e00000000 0xf68d3888f8000000

def z92 : W := mkw 0x2fffbfbe308a11be 0x08bffefef8c22846 0xbffffffe718e1ffb 0xfefffffff9c6387f

def z93 : W := mkw 0x0010d4f20635ae74 0xb4004353c818d6b9 0x80b1fffe0e7ffffd 0xfa02c7fff839ffff

def z94 : W := mkw 0x0a80000148000001 0x002a000005200000 0xdf800001fe00000f 0x1f7e000007f80000

def z95 : W := mkw 0x0002000020880000 0x0000080000822000 0x334e000071800002 0x04cd380001c60000

def z96 : W := mkw 0x000000008150a600 0x1000000002054298 0xc040203981f3e737 0xa7010080e607cf9c

def z97 : W := mkw 0x0106220cb1dab788 0x1804188832c76ade 0xf34e223ff1ffffff 0xf7cd3888ffc7ffff

def z98 : W := mkw 0x0470d4f28775ae74 0xb411c353ca1dd6b9 0x4cb1ddc18e71e004 0x0932c7770639c780

def z99 : W := mkw 0x0100220010021000 0x0004008800400840 0x930022007002182b 0x964c008801c00860

def z100 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xbffffffe7002182b 0xfefffffff9c00860

def z101 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x5cb1c001fffc001f 0x0972c70007fff000

def z102 : W := mkw 0x0100224012031800 0x2004008900480c60 0x938033c07e03982f 0x9e4e00cf01f80e60

def z103 : W := mkw 0x0000004002010800 0x2000000100080420 0x808013c00e01982d 0x9a02004f00380660

def z104 : W := mkw 0x0576363cb1dab7b8 0x1815d8d8f2c76ade 0xff7e3e3ff1ffffff 0xfffdf8f8ffc7ffff

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c001c018001e004 0x0930007006000780

def z106 : W := mkw 0x0ff03f71db53fe31 0x303fc0fdc76d4ff8 0xdff03ff9fff3ff3f 0xbf7fc0ffe7ffcffc

def z107 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x8081d3c60e0d98ed 0xda02074f18383663

def z108 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xaf8fffc600000000 0xdebe3fff18000000

def z109 : W := mkw 0x01002b4012035800 0x200400ad00480d60 0x00003fc00003f820 0x800000ff00000fe0

def z110 : W := mkw 0x146b4000a5ec0000 0xc051ad000297b000 0x207fc00001fc0010 0x6081ff000007f000

def z111 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703e3f81ffffff 0xff31c0f8fe07ffff

def z112 : W := mkw 0x0b90fbe35e37dc65 0xb42e43ef8d78df71 0xdfb1ffe7fe7ffcff 0xff7ec7ff9ff9fff3

def z113 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0x207fc03e00000000 0x6081ff00f8000000

def z114 : W := mkw 0x0000400004240000 0x8000010000109000 0x00b1c0000e700004 0x0802c7000039c000

def z115 : W := mkw 0x0460041081402210 0x0011801042050088 0x4c402c1981826302 0x053100b06606098c

def z116 : W := mkw 0x1efb5021edfc8421 0xd07bed4087b7f210 0xffffd021fffd843f 0xffffff4087fff610

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040223e018e1ffb 0xf6010088f806387f

def z118 : W := mkw 0x0460041081402210 0x0011801042050088 0xcc702c1981f26317 0x2f31c0b06607c98c

def z119 : W := mkw 0x001090a200000024 0x0000424288000000 0x80b1d3e600000000 0xfa02c74f98000000

def z120 : W := mkw 0x047054708775ae70 0xb411c151c21dd6b9 0xcc703c398fffffff 0xaf31c0f0e63fffff

def z121 : W := mkw 0x0010102000108420 0x1000404080004210 0x80301226007d9cfd 0xfa00c0489801f673

def z122 : W := mkw 0x0fed220c00000008 0x003fb48830000000 0xafffe23e00000000 0xfebfff88f8000000

def z123 : W := mkw 0x2ef99db28150a636 0x10bbe676ca054298 0xccf1fdf981f3e737 0xaf33c7f7e607cf9c

def z124 : W := mkw 0x3fffffbfedec003f 0xc0fffffeffb7b000 0xfffffffffffc001f 0xfffffffffffff000

def z125 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc227fffc1cff 0xffffff089ffff073

def z126 : W := mkw 0x0000004002010800 0x2000000100080420 0x000000000e01982d 0x0000000000380660

def z127 : W := mkw 0x0000404006250800 0xa000010100189420 0x80b1d3c00e7d983d 0xfa02c74f0039f660

def z128 : W := mkw 0x0006000c308a1188 0x0800180030c22846 0x304e003e718e1ffb 0x60c13800f9c6387f

def z129 : W := mkw 0x0470d4f28775ae74 0xb411c353ca1dd6b9 0xccb1dfe78e7dfcfd 0xfb32c77f9e39f7f3

def z130 : W := mkw 0x1a8b4001edec0001 0xc06a2d0007b7b000 0x738fc001fffc001f 0x51ce3f0007fff000

def z131 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0xb3bfc0007e7c001d 0x7aceff0001f9f000

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x808013c000000000 0x9a02004f00000000

def z133 : W := mkw 0x2fffbfbeb1dab7be 0x18bffefefac76ade 0xfffffffff1ffffff 0xffffffffffc7ffff

def z134 : W := mkw 0x057036309152b630 0x1015c0d8c2454ad8 0xdf703e39f1f3ff3f 0xbf7dc0f8e7c7cffc

def z135 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xff4e3e3ff18fffff 0xfffd38f8ffc63fff

def z136 : W := mkw 0x0000000148000001 0x0000000005200000 0x50000001fe00000f 0x0140000007f80000

def z137 : W := mkw 0x0460000081400000 0x0011800002050000 0xcc70000181f00017 0x2f31c0000607c000

def z138 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xaffffffe00718435 0xfebffffff801c610

def z139 : W := mkw 0x000000008150a600 0x1000000002054298 0x400000018071e004 0x010000000601c780

def z140 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3e60e718004 0xfa02c74f9839c600

def z141 : W := mkw 0x0b802b0148000001 0x002e00ac05200000 0xdf803fc1fe00000f 0x9f7e00ff07f80000

def z142 : W := mkw 0x0ee9400004240000 0x803ba50000109000 0xafffc0000e7c001d 0x7ebfff000039f000

def z143 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfc03ff9ff83ff3f 0xbf7f00ffe7fe0ffc

def z144 : W := mkw 0x0a80000148000001 0x002a000005200000 0xdf803c01fe03e02f 0x9f7e00f007f80f80

def z145 : W := mkw 0x0000404006358c40 0xb40001010018d631 0x000000000e7d9cfd 0x000000000039f673

def z146 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d1c00e718004 0x0802c7470039c600

def z147 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e201871820302 0x04cd388061c6080c

def z148 : W := mkw 0x0ff03f71db53fe31 0x303fc0fdc76d4ff8 0xdfb03fc1fe73f82f 0x9f7ec0ff07f9cfe0

def z149 : W := mkw 0x0566261cb1ca3398 0x0815989872c728ce 0x7f4e2c19f1826302 0x05fd38b067c6098c

def z150 : W := mkw 0x1feb6201fdee1001 0xc07fad8807f7b840 0xffffe201fffe183f 0xffffff8807fff860

def z151 : W := mkw 0x001090e202010824 0x2000424388080420 0x80b1d3e60e01982d 0xfa02c74f98380660

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000206000c18c8 0x5000000818003063

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040201801820302 0x040100806006080c

def z154 : W := mkw 0x01002b4012035800 0x200400ad00480d60 0x93003fc07003f82b 0x964c00ff01c00fe0

def z155 : W := mkw 0x2b9dbfbe0000003e 0x00ae76fef8000000 0x238ffffe00000000 0xd08e3ffff8000000

def z156 : W := mkw 0x1feb6b01fdee5001 0xc07fadac07f7b940 0xffffec01fffe601f 0x7fffffb007fff980

def z157 : W := mkw 0x0b806b415e275801 0xa02e01ad05789d60 0xdfb1ffc1fe7ff83f 0xff7ec7ff07f9ffe0

def z158 : W := mkw 0x0a8009414a014801 0x202a002505280520 0xdf801dc1fe01e00f 0x1f7e007707f80780

def z159 : W := mkw 0x0470143000000030 0x0011c050c0000000 0x8c703c3800000000 0xae31c0f0e0000000

def z160 : W := mkw 0x01022200308a1000 0x0004088800c22840 0xb34e2200718e183b 0xf6cd388801c63860

def z161 : W := mkw 0x0fe92b0000000000 0x003fa4ac00000000 0xafffffc000000000 0xfebfffff00000000

def z162 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d1e00e718435 0xaa02c7478039c610

def z163 : W := mkw 0x0000400004348440 0x940001000010d211 0x00000000007c04d0 0x000000000001f013

def z164 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c303c398073e724 0x8930c0f0e601cf9c

def z165 : W := mkw 0x0b862b4d7a8b5989 0x282e18ad35ea2d66 0xb3ce23fe7f8e1ffb 0xf6cf388ff9fe387f

def z166 : W := mkw 0x1feb6b41ffef5801 0xe07fadad07ffbd60 0xffffc3c1fffc181f 0x7fffff0f07fff060

def z167 : W := mkw 0x1efbd4f3effdae75 0xf47bef53cfbff6b9 0xffffffffffffffff 0xffffffffffffffff

def z168 : W := mkw 0x200d808e0000000e 0x0080360238000000 0x200fc00600000000 0x40803f0018000000

def z169 : W := mkw 0x0566261cb1ca3398 0x0815989872c728ce 0xff4e2e3ff18e7ffb 0xf7fd38b8ffc639ff

def z170 : W := mkw 0x0fe02f11d9427211 0x003f80bc476509c8 0x5f402c19f1826302 0x057d00b067c6098c

def z171 : W := mkw 0x0ef914308150a630 0x103be450c2054298 0xeffffc3981f3e737 0xffbffff0e607cf9c

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000c1cf9 0x0000000000003073

def z173 : W := mkw 0x0b802b0158025001 0x002e00ac05600940 0x5f002c01f0026002 0x057c00b007c00980

def z174 : W := mkw 0x0b86220d788a1189 0x082e188835e22846 0xffce223fff8e1fff 0xffff3888fffe387f

def z175 : W := mkw 0x0a8000415a035801 0x202a000105680d60 0xdf800001fe03f82f 0x1f7e000007f80fe0

def z176 : W := mkw 0x2b9dbbae0000002e 0x00ae76eeb8000000 0xa3bfd3e600000000 0xfa8eff4f98000000

def z177 : W := mkw 0x1efb5431edec0031 0xc07bed50c7b7b000 0xfffffc39fffc001f 0xfffffff0e7fff000

def z178 : W := mkw 0x2b8d2b0c0000000a 0x00ae34ac30000000 0x230e000000000000 0x008c380000000000

def z179 : W := mkw 0x01002b0000000000 0x000400ac00000000 0x00003fc000000000 0x800000ff00000000

def z180 : W := mkw 0x0104220c10021188 0x0804108830400846 0xa34e223e00021fe0 0xf68d3888f800087f

def z181 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0x338fc0007e0c0008 0x50ce3f0001f83000

def z182 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x0031c0260e7d9cfd 0x6000c7009839f673

def z183 : W := mkw 0x10024041effd8c41 0xf440090107bff631 0x50000001fffd9cff 0x0140000007fff673

def z184 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7f4e0001fffc001f 0x05fd380007fff000

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040203801820733 0xa6010080e006081c

def z186 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0xff8fc001fe0c000f 0x5ffe3f0007f83000

def z187 : W := mkw 0x000000415a035801 0x2000000105680d60 0xdc003c01fe03f82f 0x8f7000f007f80fe0

def z188 : W := mkw 0x01062b4c328b5988 0x280418ad30ca2d66 0xb34e3ffe718ffffb 0xf6cd38fff9c63fff

def z189 : W := mkw 0x2114fffe06358c7e 0xb48453fff818d631 0x80b1fffe0e7d9cfd 0xfa02c7fff839f673

def z190 : W := mkw 0x1ffff2efffff9ded 0xfc7fffcbbffffe77 0xfffff3ffffff9fff 0xffffffcffffffe7f

def z191 : W := mkw 0x001090a200108464 0x1400424288004211 0x00000026000004c0 0x0000000098000013

def z192 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e223e71820302 0xf6cd3888f9c6080c

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0x930000007000000b 0x164c000001c00000

def z194 : W := mkw 0x0470d4f206358c74 0xb411c353c818d631 0x8cf1fffe0e7d9cfd 0xfe33c7fff839f673

def z195 : W := mkw 0x0010d0a204348464 0x940043428810d211 0x80b1d3e6007c04d0 0xfa02c74f9801f013

def z196 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x0081c1c00e000000 0x0002070700380000

def z197 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x80b1c3c60e7c18dd 0x7a02c70f1839f063

def z198 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x330e0206718e1ffb 0x50cc380819c6387f

def z199 : W := mkw 0x001090e202118c64 0x3400424388084631 0x800013e6000d9cf9 0xf200004f98003673

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040000001800013 0x2601000000060000

def z201 : W := mkw 0x01002b4012035800 0x200400ad00480d60 0xcc003fc18003f827 0x8f3000ff06000fe0

def z202 : W := mkw 0x0010102000108420 0x1000404080004210 0x0030002000700410 0x2000c0008001c010

def z203 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fcfc001ff8c000a 0x55ff3f0007fe3000

def z204 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e223e71821fe2 0x84cd3888f9c6087f

def z205 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f801fc1fe01f80c 0x197e007f07f807e0

def z206 : W := mkw 0x04620000a1c80000 0x0011880002872000 0xff7e0001f1fc001f 0x7ffdf80007c7f000

def z207 : W := mkw 0x0b862b4d7a8b5989 0x282e18ad35ea2d66 0x338e03c67e0c18c8 0x50ce380f19f83063

def z208 : W := mkw 0x2ff9bfb200000036 0x00bfe6fec8000000 0x8fb1ffc000000000 0x9e3ec7ff00000000

def z209 : W := mkw 0x001094f20211ae74 0x34004253c80846b9 0x00003ffe0003ffe0 0x800000fff8000fff

def z210 : W := mkw 0x0576363cb1dab7b8 0x1815d8d8f2c76ade 0xff7e3c39f1f3e737 0xaffdf8f0e7c7cf9c

def z211 : W := mkw 0x0010d0a204348464 0x940043428810d211 0x0031c026007c04d0 0x6000c7009801f013

def z212 : W := mkw 0x0010143000000030 0x00004050c0000000 0x00003c3800000000 0x800000f0e0000000

def z213 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fe7fe0ffcff 0xff7e00ff9ff83ff3

def z214 : W := mkw 0x1ef9d0e3cf758c65 0xf47be7438f3dd631 0x4cb1d1c18e718004 0x0932c7470639c600

def z215 : W := mkw 0x0476143ca1d8a7b8 0x1811d850f287629e 0xec7e3c3f81ffe7f7 0xefb1f8f0fe07ff9f

def z216 : W := mkw 0x0000404006250840 0xa400010100189421 0x000000000e0c18c8 0x0000000000383063

def z217 : W := mkw 0x2fed2f1c8140221a 0x00bfb4bc72050088 0x6f4e2c1981826302 0x05bd38b06606098c

def z218 : W := mkw 0x1eeb0001e9c80001 0x407bac0007a72000 0xff4e0001f18c001b 0x77fd380007c63000

def z219 : W := mkw 0x147bd0a2a5fc8464 0xd451ef428a97f211 0x207fc02601fc04d0 0x6081ff009807f013

def z220 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3c00e71982d 0x9a02c74f0039c660

def z221 : W := mkw 0x0a8009415a035801 0x202a002505680d60 0x5c801dc1fe03f82f 0x0972007707f80fe0

def z222 : W := mkw 0x100b400024ac0000 0xc0402d000092b000 0x200fc000000c0000 0x40803f0000003000

def z223 : W := mkw 0x2ffdbfbf4800003f 0x00bff6fefd200000 0xfffffffffe00000f 0xfffffffffff80000

def z224 : W := mkw 0x10024000a5ec0000 0xc04009000297b000 0x0000000001fc0010 0x000000000007f000

def z225 : W := mkw 0x0460400085640000 0x8011810002159000 0xccf1c0018ffc001f 0x7f33c700063ff000

def z226 : W := mkw 0x147b5430a5fca630 0xd051ed50c297f298 0x207fc03801fc0710 0x6081ff00e007f01c

def z227 : W := mkw 0x0a90d0e34e358c65 0xb42a43438d38d631 0xdfb1d3e7fe7d9cff 0xff7ec74f9ff9f673

def z228 : W := mkw 0x0010d0e35e37dc65 0xb40043438d78df71 0xd0b1d3e7fe7ffcff 0xfb42c74f9ff9fff3

def z229 : W := mkw 0x3fffffffeffd8c7f 0xf4ffffffffbff631 0xfffffffffffd9cff 0xfffffffffffff673

def z230 : W := mkw 0x2ffdbfffdb53fe3f 0x30bff6ffff6d4ff8 0xfffffffffff3ff3f 0xffffffffffffcffc

def z231 : W := mkw 0x001090e202118c64 0x3400424388084631 0x000011c000018000 0x0000004700000600

def z232 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fbfdfc600000000 0x58beff7f18000000

def z233 : W := mkw 0x0460000081400000 0x0011800002050000 0x4c30000180700004 0x0930c0000601c000

def z234 : W := mkw 0x2ffdbfbe8140003e 0x00bff6fefa050000 0xefffffff81f00017 0xffbffffffe07c000

def z235 : W := mkw 0x1ee94001cd640001 0xc07ba50007359000 0xdfb1c001fe70000f 0x1f7ec70007f9c000

def z236 : W := mkw 0x0000000010021180 0x0800000000400846 0x0000000000021fe0 0x000000000000087f

def z237 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e0206718c18db 0x76cd380819c63063

def z238 : W := mkw 0x257fb6be308a11be 0x0895fedaf8c22846 0xb37fe23e718e1ffb 0xf6cdff88f9c6387f

def z239 : W := mkw 0x001090a200000024 0x0000424288000000 0x00b1d1c000000000 0x0802c74700000000

def z240 : W := mkw 0x000000008150a600 0x1000000002054298 0x0000000001f00710 0x000000000007c01c

def z241 : W := mkw 0x3fef2f1de9c8001b 0x40ffbcbc77a72000 0x7f4e2c19f1800002 0x05fd38b067c60000

def z242 : W := mkw 0x2104ab8e0000000e 0x008412ae38000000 0x000003c600000000 0x0000000f18000000

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040003801800710 0x20010000e006001c

def z244 : W := mkw 0x2ffdfffe8775ae7e 0xb4bff7fffa1dd6b9 0xefffffff8fffffff 0xffbffffffe3fffff

def z245 : W := mkw 0x047014708351ae30 0x3011c051c20d46b8 0xccf03ff98ff3ff3f 0xbf33c0ffe63fcffc

def z246 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x330e223e700e1fe8 0xd0cc3888f9c0387f

def z247 : W := mkw 0x1b8f620d7cae1189 0xc86e3d8835f2b846 0xb3cfe23e7f8e1ffb 0xf6cf3f88f9fe387f

def z248 : W := mkw 0x2b8fab8e308a118e 0x08ae3eae38c22846 0xb3cfe3fe718e1ffb 0xf6cf3f8ff9c6387f

def z249 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e203e718e07d2 0x64cd3880f9c6381f

def z250 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0x0cb1c00000000000 0x0832c70000000000

def z251 : W := mkw 0x0016d0ae24bc85ec 0x9c005b42b892f217 0x207fc03e01fc07d0 0x6081ff00f807f01f

def z252 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffe039fffe073f 0xffffff80e7fff81c

def z253 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x33ffc0007ffc0018 0x70cfff0001fff000

def z254 : W := mkw 0x0000808200000004 0x0000020208000000 0x0081c3c600000000 0x5002070f18000000

def z255 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fffc001fff00006 0x0dffff0007ffc000

def z256 : W := mkw 0x2fed2f1c0000001a 0x00bfb4bc70000000 0xaf4e2e3e00000000 0xf6bd38b8f8000000

def z257 : W := mkw 0x00020000308a1180 0x0800080000c22846 0x1000000071820302 0x0040000001c6080c

def z258 : W := mkw 0x0004000c00000008 0x0000100030000000 0x204e003e00000000 0x60813800f8000000

def z259 : W := mkw 0x0b802b0000000000 0x002e00ac00000000 0xcf803fc18003e027 0x9f3e00ff06000f80

def z260 : W := mkw 0x04721430a1d8a630 0x1011c850c2876298 0xff7e3c39f1ffe73f 0xfffdf8f0e7c7ff9c

def z261 : W := mkw 0x0000000081400000 0x0000000002050000 0x4000000181f00017 0x010000000607c000

def z262 : W := mkw 0x0104220c10021188 0x0804108830400846 0x9300223e70021feb 0x964c0088f9c0087f

def z263 : W := mkw 0x2114bffe1203583e 0x208452fff8480d60 0x00003ffe0003f820 0x800000fff8000fe0

def z264 : W := mkw 0x0106220c20880188 0x0804188830822006 0xa34e223e018c07d0 0xf68d3888f806301f

def z265 : W := mkw 0x0100220010021000 0x0004008800400840 0x0000220000021820 0x8000008800000860

def z266 : W := mkw 0x0116363c309ab7b8 0x180458d8f0c26ade 0xb34e3e3e718ffffb 0xf6cd38f8f9c63fff

def z267 : W := mkw 0x0000000000000000 0x0000000000000000 0x8030000000700015 0x2a00c0000001c000

def z268 : W := mkw 0x2ffdfffe0625087e 0xa4bff7fff8189421 0xaffffffe0e0c18c8 0xfebffffff8383063

def z269 : W := mkw 0x2ffd3f3c0000003a 0x00bff4fcf0000000 0xaf7e3c3800000000 0xaebdf8f0e0000000

def z270 : W := mkw 0x1469400085640000 0xc051a50002159000 0x0031c00000700000 0x0000c7000001c000

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z272 : W := mkw 0x0010102000108420 0x1000404080004210 0x0000102000018420 0x8000004080000610

def z273 : W := mkw 0x01002b4012035800 0x200400ad00480d60 0x000003c000001800 0x0000000f00000060

def z274 : W := mkw 0x247d94be8150a63e 0x1091f652fa054298 0x207fc03e01f00710 0x6081ff00f807c01c

def z275 : W := mkw 0x1eeb0001e9c80001 0x407bac0007a72000 0xff7e0001f1f00017 0x2ffdf80007c7c000

def z276 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2f7fec3e00000000 0x64bdffb0f8000000

def z277 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0xa0ffd3fe00000000 0xfa83ff4ff8000000

def z278 : W := mkw 0x0002000020880000 0x0000080000822000 0xb34e0226718c1cfb 0xf6cd380899c63073

def z279 : W := mkw 0x2b8dabcf5a03580f 0x20ae36af3d680d60 0x338fc3c67e001808 0x50ce3f0f19f80060

def z280 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe01820733 0xfebffffff806081c

def z281 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3c60e7d98cc 0x5802c74f1839f663

def z282 : W := mkw 0x0b802b0158025001 0x002e00ac05600940 0xdf003c01f003e027 0x8f7c00f007c00f80

def z283 : W := mkw 0x1eeb4000a5ec0000 0xc07bad000297b000 0xafffc00001fc0010 0x7ebfff000007f000

def z284 : W := mkw 0x1ffbfbe3ffffdc65 0xf47fefef8fffff71 0xffffffe7fffffcff 0xffffffff9ffffff3

def z285 : W := mkw 0x21042f1c0000001a 0x008410bc70000000 0x00002c1800000000 0x000000b060000000

def z286 : W := mkw 0x0000400004240000 0x8000010000109000 0x80b1c2260e7c1cfd 0xfa02c7089839f073

def z287 : W := mkw 0x1b8f620d7cae1189 0xc86e3d8835f2b846 0x338fc2067e0c18c8 0x50ce3f0819f83063

def z288 : W := mkw 0x1ef95431cd74a631 0xd07be550c735d298 0x4cb1dc018e71e004 0x0932c7700639c780

def z289 : W := mkw 0x1eebc0c3efed0845 0xe47baf030fbfb421 0xffffc3c7fffc18df 0x7fffff0f1ffff063

def z290 : W := mkw 0x0460041000000010 0x0011801040000000 0x0c402c1800000000 0x043100b060000000

def z291 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000200000020023 0x8600008000000800

def z292 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0x2cffddfe00000000 0x68b3ff77f8000000

def z293 : W := mkw 0x0a82000168880001 0x002a080005a22000 0xffce0001ff8c001f 0x7fff380007fe3000

def z294 : W := mkw 0x1fef220df9ca1189 0x487fbc8837e72846 0x7f4e2019f1820302 0x05fd388067c6080c

def z295 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0xafffc00000000000 0x7ebfff0000000000

def z296 : W := mkw 0x0b802b0158025001 0x002e00ac05600940 0xdf802c01fe02600f 0x1f7e00b007f80980

def z297 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x6cffc0018ffc0014 0x69b3ff00063ff000

def z298 : W := mkw 0x1eef400dedec0189 0xc87bbd0037b7b006 0xffffc03ffffc07df 0x7fffff00fffff01f

def z299 : W := mkw 0x0460000081400000 0x0011800002050000 0xcc70203981f20737 0xaf31c080e607c81c

def z300 : W := mkw 0x3fffbfbfe9c8003f 0x40fffefeffa72000 0xfffffffff1800002 0xffffffffffc60000

def z301 : W := mkw 0x0b862b0d788a5189 0x082e18ac35e22946 0x7f4e2c19f1826302 0x05fd38b067c6098c

def z302 : W := mkw 0x0010d0e28775ae64 0xb40043438a1dd6b9 0xc0b1d3e78fffffff 0xfb02c74f9e3fffff

def z303 : W := mkw 0x0470143000000030 0x0011c050c0000000 0xcc703c398003e027 0xaf31c0f0e6000f80

def z304 : W := mkw 0x0002400024ac0000 0x800009000092b000 0xb3ffc0007ffc001f 0x7ecfff0001fff000

def z305 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e203871820733 0xa6cd3880e1c6081c

def z306 : W := mkw 0x1efb5431edfca631 0xd07bed50c7b7f298 0xffffdc01fffde01f 0x7fffff7007fff780

def z307 : W := mkw 0x0fe02f51db437a11 0x203f80bd476d0de8 0xdfc03fd9ff83fb2f 0x9f7f00ff67fe0fec

def z308 : W := mkw 0x156f620cb5ee1188 0xc855bd8832d7b846 0xb37fe23e71fe1ffb 0xf6cdff88f9c7f87f

def z309 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f003fc1f003f822 0x857c00ff07c00fe0

def z310 : W := mkw 0x0ff63f7dfbdbffb9 0x383fd8fdf7ef6ffe 0xfffe3fffffffffff 0xfffff8ffffffffff

def z311 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00000180000007 0x0f30000006000000

def z312 : W := mkw 0x0106e2ce36af19cc 0xac041b8b38dabc67 0x338fc3c67e0c18c8 0x50ce3f0f19f83063

def z313 : W := mkw 0x000000415a035801 0x2000000105680d60 0xd08013c1fe03f82f 0x9b42004f07f80fe0

def z314 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80f1f3fe0fff9fff 0xfe03c7cff83ffe7f

def z315 : W := mkw 0x0b842b4d5a035989 0x282e10ad35680d66 0xdf803ffffe03ffef 0x9f7e00fffff80fff

def z316 : W := mkw 0x0106224d7a8b5989 0x2804188935ea2d66 0xf34e223fff8fffff 0xf7cd3888fffe3fff

def z317 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f802fc1fe02780a 0x157e00bf07f809e0

def z318 : W := mkw 0x2ffdbfbe8140223e 0x00bff6fefa050088 0xefffffff81826302 0xffbffffffe06098c

def z319 : W := mkw 0x1a8bc0c36ead0845 0xe46a2f030dbab421 0x338fc3c67e0c18c8 0x50ce3f0f19f83063

def z320 : W := mkw 0x001010208150a620 0x1000404082054298 0xc030102181f3e737 0xab00c0408607cf9c

def z321 : W := mkw 0x0a89000000000000 0x002a240000000000 0x238fc00000000000 0x508e3f0000000000

def z322 : W := mkw 0x1eeb4411edec2211 0xc07bad1047b7b088 0xffffec19fffe631f 0x7fffffb067fff98c

def z323 : W := mkw 0x2ffdbfbf5802503f 0x00bff6fefd600940 0xfffffffff0026002 0xffffffffffc00980

def z324 : W := mkw 0x0100220010021000 0x0004008800400840 0x1300020070001808 0x104c000801c00060

def z325 : W := mkw 0x147b5430a5fca630 0xd051ed50c297f298 0xec7ffc3981ffe737 0xefb1fff0e607ff9c

def z326 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe000c1cf9 0xfebffffff8003073

def z327 : W := mkw 0x2574bfbe0000003e 0x0095d2fef8000000 0x8c703ffe00000000 0xae31c0fff8000000

def z328 : W := mkw 0x0b90fbe206358c64 0xb42e43ef8818d631 0x8fb1ffe60e7d9cfd 0xfe3ec7ff9839f673

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x808000000e00000d 0x1a02000000380000

def z330 : W := mkw 0x0110bbe21213dc64 0x340442ef88484f71 0x00003fe60003fce0 0x800000ff98000ff3

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000100000018025 0x8a00004000000600

def z332 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0x2f4e000000000000 0x04bd380000000000

def z333 : W := mkw 0x0b822b417a8b5801 0x202e08ad05ea2d60 0xffce3fc1ff8ff83f 0xffff38ff07fe3fe0

def z334 : W := mkw 0x2b9dfbee06358c6e 0xb4ae77efb818d631 0xa3bfd3e60e7d9cfd 0xfa8eff4f9839f673

def z335 : W := mkw 0x00020000308a1180 0x0800080000c22846 0x90402038718e1ffb 0xa6410080e1c6387f

def z336 : W := mkw 0x1eeb4041efed0801 0xe07bad0107bfb420 0xffffd3c1fffd983f 0xffffff4f07fff660

def z337 : W := mkw 0x0a80000148000001 0x002a000005200000 0x5f000001f0000002 0x057c000007c00000

def z338 : W := mkw 0x04721430b1dab7b0 0x1811c850c2c76ade 0xdc703c39f1ffffff 0xaf71c0f0e7c7ffff

def z339 : W := mkw 0x0104220c10021188 0x0804108830400846 0x00000206000018c0 0x0000000818000063

def z340 : W := mkw 0x000040415e37dc41 0xb40001010578df71 0x50000001fe7ffcff 0x0140000007f9fff3

def z341 : W := mkw 0x1eeb4941efed4801 0xe07bad2507bfb520 0xffffddc1fffde01f 0x7fffff7707fff780

def z342 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x23ffc3fe00000000 0x708fff0ff8000000

def z343 : W := mkw 0x0a90d9e34e35cc65 0xb42a43678d38d731 0x4cb1ddc18e71e004 0x0932c7770639c780

def z344 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4070003981f3e737 0x2101c000e607cf9c

def z345 : W := mkw 0x0000000081402200 0x0000000002050088 0x4000000181826302 0x010000000606098c

def z346 : W := mkw 0x2fffbfbe308a11be 0x08bffefef8c22846 0xbffffffe700c18c8 0xfefffffff9c03063

def z347 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc701c0181f1e017 0x2f31c0700607c780

def z348 : W := mkw 0x0ef9143000000030 0x003be450c0000000 0xaffffc3800000000 0xfebffff0e0000000

def z349 : W := mkw 0x00020000308a1180 0x0800080000c22846 0x10000000700c18c8 0x0040000001c03063

def z350 : W := mkw 0x147bd0e2a7fd8c64 0xf451ef438a9ff631 0xa0ffd3e60ffd9cfd 0xfa83ff4f983ff673

def z351 : W := mkw 0x347fd4bea5ec003e 0xc0d1ff52fa97b000 0x207fc03e01fc0010 0x6081ff00f807f000

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0x80b1c00000000000 0x7a02c70000000000

def z353 : W := mkw 0x001014300010a630 0x10004050c0004298 0x80403c380183e733 0xa60100f0e0060f9c

def z354 : W := mkw 0x0b90bba200000024 0x002e42ee88000000 0x8fb1ffe600000000 0xfe3ec7ff98000000

def z355 : W := mkw 0x0470d4b28574a674 0x9411c352ca15d299 0xcc71fc3f81ffe7f7 0xef31c7f0fe07ff9f

def z356 : W := mkw 0x047054308574a630 0x9011c150c215d298 0xccf1fc398fffe73f 0xff33c7f0e63fff9c

def z357 : W := mkw 0x1feb2b41fbcb5801 0x607facad07ef2d60 0xffce3fc1ff83f82f 0x9fff38ff07fe0fe0

def z358 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x8081c3e60e0c1cf9 0xf202070f98383073

def z359 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x0030000000700000 0x0000c0000001c000

def z360 : W := mkw 0x0116f2ae34be95ec 0x9c045bcab8d2fa57 0xb37fe23e71fe1ffb 0xf6cdff88f9c7f87f

def z361 : W := mkw 0x0a8009414a014801 0x202a002505280520 0xcc801fc18e01f82d 0x9b32007f063807e0

def z362 : W := mkw 0x0116b2ee329b9dec 0x3c045acbb8ca6e77 0xb34e33fe718f9ffb 0xf6cd38cff9c63e7f

def z363 : W := mkw 0x2fef2f1c308a119a 0x08bfbcbc70c22846 0x3f4e2c1871820302 0x04fd38b061c6080c

def z364 : W := mkw 0x2ef99df34a014837 0x20bbe677cd280520 0x4cb1ddc18e01e004 0x0932c77706380780

def z365 : W := mkw 0x0ef990a200000024 0x003be64288000000 0xafffd3e600000000 0xfebfff4f98000000

def z366 : W := mkw 0x0eeb000020880000 0x003bac0000822000 0xbfffc000718c001b 0x7effff0001c63000

def z367 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xefffffff8003e027 0xffbffffffe000f80

def z368 : W := mkw 0x047094b200000034 0x0011c252c8000000 0x8cf1fffe00000000 0xfe33c7fff8000000

def z369 : W := mkw 0x0104220c00000008 0x0004108830000000 0x230e020600000000 0x508c380818000000

def z370 : W := mkw 0x2ef9ddf206358c76 0xb4bbe777c818d631 0x8cb1dfe60e7d9cfd 0xfa32c77f9839f673

def z371 : W := mkw 0x3fffffbfedfca63f 0xd0fffffeffb7f298 0xffffffffffffe73f 0xffffffffffffff9c

def z372 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf8003c1fe00180f 0x1f7e000f07f80060

def z373 : W := mkw 0x10024041ffef5801 0xe040090107ffbd60 0x50000001fffff83f 0x0140000007ffffe0

def z374 : W := mkw 0x0fe02b41db435801 0x203f80ad076d0d60 0xdff03fc1fff3f83f 0xbf7fc0ff07ffcfe0

def z375 : W := mkw 0x0b802b0000000000 0x002e00ac00000000 0x038003c000000000 0x100e000f00000000

def z376 : W := mkw 0x0ff03f31d952f631 0x103fc0fcc7654bd8 0xdf703c39f1f3e737 0xaf7dc0f0e7c7cf9c

def z377 : W := mkw 0x0000004002010800 0x2000000100080420 0x008011c00e018004 0x0802004700380600

def z378 : W := mkw 0x2fffbfbe2088003e 0x00bffefef8822000 0xbffffffe718c001b 0xfefffffff9c63000

def z379 : W := mkw 0x1feb2b01f9ca5001 0x407facac07e72940 0x7f4e2c01f1826002 0x05fd38b007c60980

def z380 : W := mkw 0x2ffdbffe02118c7e 0x34bff6fff8084631 0xaffffffe00019ce0 0xfebffffff8000673

def z381 : W := mkw 0x001014300010a630 0x10004050c0004298 0x00001c000001e000 0x0000007000000780

def z382 : W := mkw 0x0470143000000030 0x0011c050c0000000 0x0c301c0000000000 0x0830c07000000000

def z383 : W := mkw 0x0010d0a204348464 0x940043428810d211 0x80b1c0260e7c04dd 0x7a02c7009839f013

def z384 : W := mkw 0x0010d0a204348464 0x940043428810d211 0x8031d026007d84f5 0xea00c7409801f613

def z385 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0xac7ffc3e00000000 0xeeb1fff0f8000000

def z386 : W := mkw 0x0ef01431c950a631 0x103bc050c7254298 0xdff03c39fff3e73f 0xbf7fc0f0e7ffcf9c

def z387 : W := mkw 0x05703f709353fe30 0x3015c0fdc24d4ff8 0xcc703ff981f3ff37 0xaf31c0ffe607cffc

def z388 : W := mkw 0x0114b2ee12139dec 0x3c0452cbb8484e77 0x000033fe00039fe0 0x800000cff8000e7f

def z389 : W := mkw 0x3fffffbf6cac003f 0xc0fffffefdb2b000 0xbffffffe7e0c0008 0xfefffffff9f83000

def z390 : W := mkw 0x1106620dfdee1189 0xc844198837f7b846 0xf34e223ffffe1fff 0xf7cd3888fffff87f

def z391 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e221e718e1bca 0x54cd388879c6386f

def z392 : W := mkw 0x0b862b0c308a1188 0x082e18ac30c22846 0xbfce3ffe718e1ffb 0xfeff38fff9c6387f

def z393 : W := mkw 0x0ff03f308150a630 0x103fc0fcc2054298 0xcff03ff981f3e737 0xbf3fc0ffe607cf9c

def z394 : W := mkw 0x0a8009414a014801 0x202a002505280520 0xcc803dc18e03e027 0x8f3200f706380f80

def z395 : W := mkw 0x0002000020880000 0x0000080000822000 0x10000000718c001b 0x0040000001c63000

def z396 : W := mkw 0x0010506006358c60 0xb40041418018d631 0x803010200e7d9cfd 0xaa00c0408039f673

def z397 : W := mkw 0x0b802b4012035800 0x202e00ad00480d60 0x8f803fc00003f820 0x9e3e00ff00000fe0

def z398 : W := mkw 0x0000c0c206358c44 0xb40003030818d631 0x0081c3c60e7d9cfd 0x5002070f1839f673

def z399 : W := mkw 0x001090a200000024 0x0000424288000000 0x80b1d3e6000c1cf9 0xfa02c74f98003073

def z400 : W := mkw 0x0104220c00000008 0x0004108830000000 0xa34e223e01820733 0xf68d3888f806081c

def z401 : W := mkw 0x1a8940014c240001 0xc06a250005309000 0x0081c0000e000000 0x0002070000380000

def z402 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb30e2206700e18eb 0xd6cc388819c03863

def z403 : W := mkw 0x2114bfbe0000003e 0x008452fef8000000 0x00003ffe00000000 0x800000fff8000000

def z404 : W := mkw 0x0000400004240000 0x8000010000109000 0x000000000e7c001d 0x000000000039f000

def z405 : W := mkw 0x01002b4012035800 0x200400ad00480d60 0x80803fc00e03f82d 0x9a0200ff00380fe0

def z406 : W := mkw 0x1eeb4041effd8c41 0xf47bad0107bff631 0xffffc001fffd9cff 0x7fffff0007fff673

def z407 : W := mkw 0x3fffffbea5ec003e 0xc0fffffefa97b000 0xaffffffe01fc0010 0xfebffffff807f000

def z408 : W := mkw 0x0b90fbe35e37dc65 0xb42e43ef8d78df71 0xdfb1ffc1fe73f82f 0x9f7ec7ff07f9cfe0

def z409 : W := mkw 0x100240016cac0001 0xc040090005b2b000 0x100000007e0c0008 0x0040000001f83000

def z410 : W := mkw 0x0114b2ae0000002c 0x000452cab8000000 0xa3fff3fe00000000 0xfe8fffcff8000000

def z411 : W := mkw 0x00000041db53fe01 0x30000001076d4ff8 0x50000001fff3ff3f 0x0140000007ffcffc

def z412 : W := mkw 0x0000404006358c40 0xb40001010018d631 0x808013c00e7d9cfd 0x9a02004f0039f673

def z413 : W := mkw 0x00020000308a1180 0x0800080000c22846 0xb34e0000718e1ffb 0x76cd380001c6387f

def z414 : W := mkw 0x0000000000108400 0x1000000000004210 0x0000000000718435 0x000000000001c610

def z415 : W := mkw 0x1ee94001cd640001 0xc07ba50007359000 0xefffc0018e700004 0x7fbfff000639c000

def z416 : W := mkw 0x010022415a035801 0x2004008905680d60 0xd3002201fe03f82f 0x974c008807f80fe0

def z417 : W := mkw 0x0000c08204240044 0x8400030208109001 0x0001c006000c00c0 0x4000070018003003

def z418 : W := mkw 0x2114bfbe0000003e 0x008452fef8000000 0x80b1fffe00000000 0xfa02c7fff8000000

def z419 : W := mkw 0x00020000308a1180 0x0800080000c22846 0x90000226718e1ffb 0xf240000899c6387f

def z420 : W := mkw 0x2ef99db28150a636 0x10bbe676ca054298 0x4cb1ddc18071e004 0x0932c7770601c780

def z421 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x0cb1fffe00000000 0x8832c7fff8000000

def z422 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d1c00e7d801d 0x7a02c7470039f600

def z423 : W := mkw 0x1eeb4001fdee1181 0xc87bad0007f7b846 0xffffc001fffe1fff 0x7fffff0007fff87f

def z424 : W := mkw 0x1ee94941cf654801 0xe07ba525073d9520 0x4cb1ddc18e71e004 0x0932c7770639c780

def z425 : W := mkw 0x0b862b4d7a8b5989 0x282e18ad35ea2d66 0xffce3fd9ff83fb2f 0x9fff38ff67fe0fec

def z426 : W := mkw 0x0b842b0c00000008 0x002e10ac30000000 0xafce3ffe00000000 0xfebf38fff8000000

def z427 : W := mkw 0x0ef01d71cb51ee31 0x303bc075c72d47b8 0xccf03df98ff3e737 0xaf33c0f7e63fcf9c

def z428 : W := mkw 0x0a80000000000000 0x002a000000000000 0x8f80000000000000 0x1e3e000000000000

def z429 : W := mkw 0x0006000c20880188 0x0800180030822006 0xb34e003e718c07db 0x76cd3800f9c6301f

def z430 : W := mkw 0x0000400004240000 0x8000010000109000 0x0031c000007c0010 0x6000c7000001f000

def z431 : W := mkw 0x0104220c10021188 0x0804108830400846 0x8000223e000e1ff9 0xf2000088f800387f

def z432 : W := mkw 0x2a89898200000006 0x00aa262608000000 0x0081c1c000000000 0x0002070700000000

def z433 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3e60e719ce4 0x8802c74f9839c673

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c003c0000000000 0x8e3000f000000000

def z435 : W := mkw 0x0b802b4002010800 0x202e00ad00080420 0x8f803fc00e01982d 0x9e3e00ff00380660

def z436 : W := mkw 0x146b4000a5ec0000 0xc051ad000297b000 0xec7fc00181fc0017 0x6fb1ff000607f000

def z437 : W := mkw 0x1feb6b01edec0001 0xc07fadac07b7b000 0xffffffc1fffc001f 0xffffffff07fff000

def z438 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c702c3981f26712 0x2531c0b0e607c99c

def z439 : W := mkw 0x001090a200000024 0x0000424288000000 0x000013e600000000 0x8000004f98000000

def z440 : W := mkw 0x0000004002118c40 0x3400000100084631 0x0000000000019ce0 0x0000000000000673

def z441 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x13803fc07e03f828 0x904e00ff01f80fe0

def z442 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d1e60e7d84d4 0x6802c7479839f613

def z443 : W := mkw 0x2ffdbfff5a03583f 0x20bff6fffd680d60 0xbffffffe7e001808 0xfefffffff9f80060

def z444 : W := mkw 0x2116bfbe308a11be 0x08845afef8c22846 0xb34e3ffe718e1ffb 0xf6cd38fff9c6387f

def z445 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e221871821b2b 0x96cd388861c6086c

def z446 : W := mkw 0x146b4000a5ec0000 0xc051ad000297b000 0xa0ffc0000ffc001d 0x7a83ff00003ff000

def z447 : W := mkw 0x047094f28351ae74 0x3411c253ca0d46b9 0xcc703fff81f3fff7 0xaf31c0fffe07cfff

def z448 : W := mkw 0x2b8debce0625084e 0xa4ae37af38189421 0x238fc3c60e0c18c8 0x508e3f0f18383063

def z449 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff8071e004 0xffbffffffe01c780

def z450 : W := mkw 0x0470143000000030 0x0011c050c0000000 0x8c703c3801820733 0xae31c0f0e006081c

def z451 : W := mkw 0x0100220010021000 0x0004008800400840 0xdf003e01f003f82f 0x9f7c00f807c00fe0

def z452 : W := mkw 0x0104220c10021008 0x0004108830400840 0xb34e223e7002182b 0xf6cd3888f9c00860

def z453 : W := mkw 0x0a8040014c240001 0x802a010005309000 0xdfb1c001fe7c001f 0x7f7ec70007f9f000

def z454 : W := mkw 0x3fefeb8fedec000f 0xc0ffbfae3fb7b000 0xffffc3c7fffc001f 0x7fffff0f1ffff000

def z455 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x1000223e718e1ffb 0x80400088f9c6387f

def z456 : W := mkw 0x10024001edfca601 0xd040090007b7f298 0x50000001ffffe73f 0x0140000007ffff9c

def z457 : W := mkw 0x047094b28150a634 0x1011c252ca054298 0xccf1ffff81f3e737 0xff33c7fffe07cf9c

def z458 : W := mkw 0x1fff763dfdfeb7b9 0xd87ffdd8f7f7fade 0xfffffe3fffffffff 0xfffffff8ffffffff

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040203800000000 0xa6010080e0000000

def z460 : W := mkw 0x0010502004348420 0x900041408010d210 0x80b1d0200e7d843d 0xfa02c7408039f610

def z461 : W := mkw 0x0470d4f28775ae74 0xb411c353ca1dd6b9 0xccf1fdf98ff3e737 0xaf33c7f7e63fcf9c

def z462 : W := mkw 0x0460000081400000 0x0011800002050000 0x4c40000181800002 0x0531000006060000

def z463 : W := mkw 0x20109db200000036 0x00804276c8000000 0x00001dc000000000 0x0000007700000000

def z464 : W := mkw 0x0ef01d71cb51ee31 0x303bc075c72d47b8 0x4cb01dc18e71e004 0x0932c0770639c780

def z465 : W := mkw 0x0460000000000000 0x0011800000000000 0x8c70000000000000 0x2e31c00000000000

def z466 : W := mkw 0x0002404036bf9dc0 0xbc00090100dafe77 0x100000007fff9fff 0x0040000001fffe7f

def z467 : W := mkw 0x2ee90d1000000012 0x00bba43440000000 0x0c000c0000000000 0x0030003000000000

def z468 : W := mkw 0x1ee94001cd640001 0xc07ba50007359000 0xccb1c0018e7c001d 0x7b32c7000639f000

def z469 : W := mkw 0x0b90bbe35a13dc65 0x342e42ef8d684f71 0xdf803fe7fe03fcef 0x9f7e00ff9ff80ff3

def z470 : W := mkw 0x0a80000148000001 0x002a000005200000 0x138000007e000008 0x104e000001f80000

def z471 : W := mkw 0x2fed2f1c0000001a 0x00bfb4bc70000000 0xafffec1800000000 0x7ebfffb060000000

def z472 : W := mkw 0x2b94bfff5a03583f 0x20ae52fffd680d60 0xdf803ffffe03f82f 0x9f7e00fffff80fe0

def z473 : W := mkw 0x0104220c00000008 0x0004108830000000 0x234e201800000000 0x048d388060000000

def z474 : W := mkw 0x0114363c1012b7b8 0x180450d8f0404ade 0x00003e3e0003ffe0 0x800000f8f8000fff

def z475 : W := mkw 0x257dbfbe0000003e 0x0095f6fef8000000 0x207ffffe00000000 0xe081fffff8000000

def z476 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e2018718e031b 0x76cd388061c6380c

def z477 : W := mkw 0x2ffd3f3c8150a63a 0x10bff4fcf2054298 0xef7e3c3981f3e737 0xafbdf8f0e607cf9c

def z478 : W := mkw 0x1ef9d0e3cf758c65 0xf47be7438f3dd631 0xccb1d3e78e7d9cfd 0xfb32c74f9e39f673

def z479 : W := mkw 0x1012d0e3effd8c65 0xf4404b438fbff631 0xd0b1d3e7fffd9cff 0xfb42c74f9ffff673

def z480 : W := mkw 0x0000400004240000 0x8000010000109000 0x0081c0000e0c0008 0x5002070000383000

def z481 : W := mkw 0x3fef6f1dedec001b 0xc0ffbdbc77b7b000 0xffffec19fffc001f 0x7fffffb067fff000

def z482 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x938013c07e01982d 0x9a4e004f01f80660

def z483 : W := mkw 0x0460000081400000 0x0011800002050000 0x0070000001f00010 0x2001c0000007c000

def z484 : W := mkw 0x0b862b4d7a8b5989 0x282e18ad35ea2d66 0xff8e3fc7fe0ff8ef 0xdffe38ff1ff83fe3

def z485 : W := mkw 0x1fef6b4dffef5989 0xe87fbdad37ffbd66 0xffffffffffffffff 0xffffffffffffffff

def z486 : W := mkw 0x0b802b414a014801 0x202e00ad05280520 0xcf803fc18e01e004 0x9f3e00ff06380780

def z487 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e2018718e1ffb 0x04cd388061c6387f

def z488 : W := mkw 0x000000000010a600 0x1000000000004298 0x000000000003e720 0x0000000000000f9c

def z489 : W := mkw 0x0b802b0158025001 0x002e00ac05600940 0xdf002e01f002782b 0x977c00b807c009e0

def z490 : W := mkw 0x0110f2e216379c64 0xb40443cb8858de71 0x93b1f3e67e7f9cff 0xfe4ec7cf99f9fe73

def z491 : W := mkw 0x0104220c00000008 0x0004108830000000 0xa34e223e000c1cf9 0xf68d3888f8003073

def z492 : W := mkw 0x10024001fdee1181 0xc840090007f7b846 0x50000001fffe1fff 0x0140000007fff87f

def z493 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c398071e004 0xaf31c0f0e601c780

def z494 : W := mkw 0x1b8b6b417eaf5801 0xe06e2dad05fabd60 0x338fc3c07e0c1808 0x50ce3f0f01f83060

def z495 : W := mkw 0x0000004002010800 0x2000000100080420 0xcc803fc18e03f82f 0x9f3200ff06380fe0

def z496 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d1c00e7d9cfd 0x0802c7470039f673

def z497 : W := mkw 0x1a9bd0e36ebd8c65 0xf46a6f438dbaf631 0xb3bfd3e67e7d9cfd 0xfaceff4f99f9f673

def z498 : W := mkw 0x0010d0a204348464 0x940043428810d211 0x0031c00000700000 0x0000c7000001c000

def z499 : W := mkw 0x0012d0e226bd8c64 0xb4004b43889af631 0xb3ffd3e67ffd9cff 0xfecfff4f99fff673

def z500 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e023e718c1fd8 0x70cd3808f9c6307f

def z501 : W := mkw 0x0006000c20880188 0x0800180030822006 0xa04e203e018e07f3 0xe6813880f806381f

def z502 : W := mkw 0x01022200308a1180 0x0804088800c22846 0x93002200718e1ffb 0x964c008801c6387f

def z503 : W := mkw 0x1efb1431e9d8a631 0x507bec50c7a76298 0xff7e3c39f1f3e737 0xaffdf8f0e7c7cf9c

def z504 : W := mkw 0x2114bfbe0010a63e 0x108452fef8004298 0x00003ffe0003e720 0x800000fff8000f9c

def z505 : W := mkw 0x0106220c20880008 0x0004188830822000 0xb34e223e718c001b 0xf6cd3888f9c63000

def z506 : W := mkw 0x0100220010021000 0x0004008800400840 0x93002226700e1cfb 0xf64c008899c03873

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000203800020720 0x80000080e000081c

def z508 : W := mkw 0x0470143000108430 0x1011c050c0004210 0x8c703c3800718435 0xae31c0f0e001c610

def z509 : W := mkw 0x0b80ebc35e275845 0xa42e03af0d789d61 0x1381c3c67e0c18c8 0x504e070f19f83063

def z510 : W := mkw 0x0116322c309a95a8 0x180458c8b0c26a56 0xb37e323e71ff9fff 0xfecdf8c8f9c7fe7f

def z511 : W := mkw 0x0476143ca1d8a7b8 0x1811d850f287629e 0x207e003e01fc07d0 0x6081f800f807f01f

def z512 : W := mkw 0x1eeb4001edfca601 0xd07bad0007b7f298 0xffffc001ffffe73f 0x7fffff0007ffff9c

def z513 : W := mkw 0x0b903b615a13dc21 0x302e40ed85684f70 0xdfb03fe1fe73fc3f 0xbf7ec0ff87f9cff0

def z514 : W := mkw 0x0002000020880180 0x0800080000822006 0x00000000018c07d0 0x000000000006301f

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0xa34e000000000000 0x768d380000000000

def z516 : W := mkw 0x0000004002010800 0x2000000100080420 0x808013e60e0d9cfd 0xfa02004f98383673

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000022600000000 0xf200000898000000

def z518 : W := mkw 0x0106224c328b1988 0x2804188930ca2c66 0xb3ce33fe7f8f9fff 0xfecf38cff9fe3e7f

def z519 : W := mkw 0x2fed2f5d5a03581b 0x20bfb4bd75680d60 0xffce3fd9fe03f82f 0x9fff38ff67f80fe0

def z520 : W := mkw 0x0b80220158021001 0x002e008805600840 0xdf802201fe02182f 0x9f7e008807f80860

def z521 : W := mkw 0x10004001cd640001 0xc040010007359000 0x400000018e700004 0x010000000639c000

def z522 : W := mkw 0x3fffffffffef583f 0xe0ffffffffffbd60 0xfffffffffffff83f 0xffffffffffffffe0

def z523 : W := mkw 0x2574bfbe8150a63e 0x1095d2fefa054298 0xcc703fff81f3e737 0xaf31c0fffe07cf9c

def z524 : W := mkw 0x2ffdffbe0434847e 0x94bff7fef810d211 0xaffffffe007c04d0 0xfebffffff801f013

def z525 : W := mkw 0x0116f2ee36bf9dec 0xbc045bcbb8dafe77 0xb3bfd3e67e7d9cfd 0xfaceff4f99f9f673

def z526 : W := mkw 0x0006000c20880188 0x0800180030822006 0x200e0006000c00c0 0x4080380018003003

def z527 : W := mkw 0x0a90d9e34e35cc65 0xb42a43678d38d731 0xccb1dfe78e7dfcfd 0xfb32c77f9e39f7f3

def z528 : W := mkw 0x1fef220df9ca1189 0x487fbc8837e72846 0xff4e223ff18e1ffb 0xf7fd3888ffc6387f

def z529 : W := mkw 0x0ff03f3000000030 0x003fc0fcc0000000 0x8ff03ff800000000 0xbe3fc0ffe0000000

def z530 : W := mkw 0x0470143081400030 0x0011c050c2050000 0xcc703c3981f00017 0xaf31c0f0e607c000

def z531 : W := mkw 0x0b96fbef7ebfdded 0xbc2e5befbdfaff77 0xffffffffffffffff 0xffffffffffffffff

def z532 : W := mkw 0x0106e2ce36af19cc 0xac041b8b38dabc67 0xb3cfe3fe7f8e1ffb 0xf6cf3f8ff9fe387f

def z533 : W := mkw 0x0100220010021000 0x0004008800400840 0x9340223871821f3b 0xb64d0088e1c6087c

def z534 : W := mkw 0x01042b4c12035988 0x280410ad30480d66 0x00003ffe0003ffe0 0x800000fff8000fff

def z535 : W := mkw 0x0470d4f28775ae74 0xb411c353ca1dd6b9 0x80f1d3fe0ffd9ffd 0xfa03c74ff83ff67f

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000002000000431 0xa200000080000010

def z537 : W := mkw 0x0576363cb1dab7b8 0x1815d8d8f2c76ade 0xb37e223e71fe1ffb 0xf6cdf888f9c7f87f

def z538 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x204e223e018e1ff0 0xe0813888f806387f

def z539 : W := mkw 0x2fed2f1d5802501b 0x00bfb4bc75600940 0x7f4e2c19f0026002 0x05fd38b067c00980

def z540 : W := mkw 0x0fe92b415a035801 0x203fa4ad05680d60 0xffffffc1fe03f82f 0xffffffff07f80fe0

def z541 : W := mkw 0x1fef620dfdee1189 0xc87fbd8837f7b846 0xffffc207fffc18df 0x7fffff081ffff063

def z542 : W := mkw 0x1fef620dedec0009 0xc07fbd8837b7b000 0xffffe23ffffc001f 0xffffff88fffff000

def z543 : W := mkw 0x001090e202118c64 0x3400424388084631 0x803013e600719cf5 0xaa00c04f9801c673

def z544 : W := mkw 0x146b4000a5ec0000 0xc051ad000297b000 0xb37fc00071fc001b 0x76cdff0001c7f000

def z545 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc70003981f00717 0x2f31c000e607c01c

def z546 : W := mkw 0x247dd4fe06358c7e 0xb491f753f818d631 0xa0ffd3fe0e7d9cfd 0xfa83ff4ff839f673

def z547 : W := mkw 0x2ffdfffe06358c7e 0xb4bff7fff818d631 0xaffffffe0e718004 0xfebffffff839c600

def z548 : W := mkw 0x0104220c10021188 0x0804108830400846 0x8040223e01821ff3 0xa6010088f806087f

def z549 : W := mkw 0x10024001edec0001 0xc040090007b7b000 0xd0b1c001fffc001f 0x7b42c70007fff000

def z550 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c701c3981f1e714 0x2931c070e607c79c

def z551 : W := mkw 0x0104220c10021188 0x0804108830400846 0x0000201800020300 0x000000806000080c

def z552 : W := mkw 0x1efb5431edfca631 0xd07bed50c7b7f298 0xffffc039fffc071f 0x7fffff00e7fff01c

def z553 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c403c398183e722 0x853100f0e6060f9c

def z554 : W := mkw 0x2efd94be0000003e 0x00bbf652f8000000 0xafffc03e00000000 0x7ebfff00f8000000

def z555 : W := mkw 0x047014300010a630 0x1011c050c0004298 0x8c703c380003e720 0xae31c0f0e0000f9c

def z556 : W := mkw 0x0ef9d0e206358c64 0xb43be7438818d631 0xafffd3e60e7d9cfd 0xfebfff4f9839f673

def z557 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0x8cb1dfe600000000 0xfa32c77f98000000

def z558 : W := mkw 0x2ffdbffe0201083e 0x20bff6fff8080420 0xaffffffe0e01982d 0xfebffffff8380660

def z559 : W := mkw 0x1eeb0001e9c80001 0x407bac0007a72000 0xffce0001ff80000f 0x1fff380007fe0000

def z560 : W := mkw 0x247dd4be0434847e 0x9491f752f810d211 0x207fc03e007c04d0 0x6081ff00f801f013

def z561 : W := mkw 0x257db6be0000003e 0x0095f6daf8000000 0xa37fe23e00000000 0xf68dff88f8000000

def z562 : W := mkw 0x0566220cb1ca1188 0x0815988832c72846 0xff7e223ff1fe1fff 0xfffdf888ffc7f87f

def z563 : W := mkw 0x201494be0000003e 0x00805252f8000000 0x0000003e00000000 0x00000000f8000000

def z564 : W := mkw 0x3ef9ddb3cd640037 0xc0fbe776cf359000 0x4cb1ddc18e700004 0x0932c7770639c000

def z565 : W := mkw 0x0b802b0158025001 0x002e00ac05600940 0x1300000070000000 0x004c000001c00000

def z566 : W := mkw 0x000080c202010844 0x2400020308080421 0x000003c6000018c0 0x0000000f18000063

def z567 : W := mkw 0x2114bffe02118c7e 0x348452fff8084631 0x00003ffe00019ce0 0x800000fff8000673

def z568 : W := mkw 0x0b806b415e37dc41 0xb42e01ad0578df71 0xdf803fc1fe7ffcff 0x9f7e00ff07f9fff3

def z569 : W := mkw 0x0000004012035800 0x2000000100480d60 0x000000000003f820 0x0000000000000fe0

def z570 : W := mkw 0x001014308150a630 0x10004050c2054298 0x40003c3981f3e737 0x810000f0e607cf9c

def z571 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2f4e3ffe00000000 0x84bd38fff8000000

def z572 : W := mkw 0x001014300010a630 0x10004050c0004298 0x80303c380073e735 0xaa00c0f0e001cf9c

def z573 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x8070203801f20733 0xa601c080e007c81c

def z574 : W := mkw 0x146f400ca5ec0188 0xc851bd003297b006 0x207fc03e01fc07d0 0x6081ff00f807f01f

def z575 : W := mkw 0x1b826b41ffef5801 0xe06e09ad07ffbd60 0xdf803fc1fffff83f 0x9f7e00ff07ffffe0

def z576 : W := mkw 0x001014300010a630 0x10004050c0004298 0x0000003800000700 0x00000000e000001c

def z577 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7f7fc001f1fc0012 0x65fdff0007c7f000

def z578 : W := mkw 0x1ee94001cd640001 0xc07ba50007359000 0xccf1c0018ff00017 0x2f33c700063fc000

def z579 : W := mkw 0x0016d0ee26bd8dec 0xbc005b43b89af637 0xa0ffd3fe0ffd9ffd 0xfa83ff4ff83ff67f

def z580 : W := mkw 0x2114bfbe100211be 0x088452fef8400846 0x00003ffe00021fe0 0x800000fff800087f

def z581 : W := mkw 0x001090a200108424 0x1000424288004210 0x80b1d3e600718435 0xfa02c74f9801c610

def z582 : W := mkw 0x0470143081402230 0x0011c050c2050088 0xcc703c3981826302 0xaf31c0f0e606098c

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000020000001829 0x9200000800000060

def z584 : W := mkw 0x000040408775ae40 0xb4000101021dd6b9 0x400000018fffffff 0x01000000063fffff

def z585 : W := mkw 0x0104220c00000008 0x0004108830000000 0x0000223e00000000 0x80000088f8000000

def z586 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x00703c3801f3e730 0xa001c0f0e007cf9c

def z587 : W := mkw 0x146b0000a1c80000 0x4051ac0002872000 0x204e000001800000 0x0081380000060000

def z588 : W := mkw 0x0010d0a204240024 0x8000434288109000 0x80b1d3e60e7c001d 0xfa02c74f9839f000

def z589 : W := mkw 0x0000404006358c40 0xb40001010018d631 0x80b1c0000e7d9cfd 0x7a02c7000039f673

def z590 : W := mkw 0x0012d0e236bf9de4 0xbc004b4388dafe77 0x90b1d3e67fff9fff 0xfa42c74f99fffe7f

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000000c0019 0x7200000000003000

def z592 : W := mkw 0x001090e202118c64 0x3400424388084631 0x808013e60e019ced 0x9a02004f98380673

def z593 : W := mkw 0x0ff0fff3df77fe75 0xb43fc3ffcf7ddff9 0xdff1ffffffffffff 0xff7fc7ffffffffff

def z594 : W := mkw 0x2fef2f1c308a119a 0x08bfbcbc70c22846 0xbf4e2e3e718e1ffb 0xf6fd38b8f9c6387f

def z595 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb30e0226700c1cf9 0xf2cc380899c03073

def z596 : W := mkw 0x0000041000002210 0x0000001040000088 0x00002c1800026300 0x000000b06000098c

def z597 : W := mkw 0x2b8dabcf5a03580f 0x20ae36af3d680d60 0xff8fffc7fe03f82f 0xdffe3fff1ff80fe0

def z598 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0x8cf1fdf800000000 0xae33c7f7e0000000

def z599 : W := mkw 0x0010106002118c20 0x3000404180084630 0x80b013e00e719c3d 0xba02c04f8039c670

def z600 : W := mkw 0x0010d0e206250864 0xa400434388189421 0x80b1d3e60e0c18c8 0xfa02c74f98383063

def z601 : W := mkw 0x01002b415a035801 0x200400ad05680d60 0x50003fc1fe03f82f 0x814000ff07f80fe0

def z602 : W := mkw 0x1ee90001c9400001 0x407ba40007250000 0x4c00000180000000 0x0130000006000000

def z603 : W := mkw 0x001090a200000024 0x0000424288000000 0x0031c02600000000 0x6000c70098000000

def z604 : W := mkw 0x0574363c00000038 0x0015d0d8f0000000 0xaf7e3e3e00000000 0xfebdf8f8f8000000

def z605 : W := mkw 0x001014300010a630 0x10004050c0004298 0xcc003c398003e727 0x8f3000f0e6000f9c

def z606 : W := mkw 0x001090e202118c64 0x3400424388084631 0x80b1d3e600019ce0 0xfa02c74f98000673

def z607 : W := mkw 0x247f94be208801be 0x0891fe52f8822006 0x207fc03e018c07d0 0x6081ff00f806301f

def z608 : W := mkw 0x0000404006358c40 0xb40001010018d631 0x000000000e718004 0x000000000039c600

def z609 : W := mkw 0x0006000c20880188 0x0800180030822006 0xa04e023e018c1ff9 0xf2813808f806307f

def z610 : W := mkw 0x10024001edec0001 0xc040090007b7b000 0xf34e0001fffc001f 0x77cd380007fff000

def z611 : W := mkw 0x0b903f715a13fe31 0x302e40fdc5684ff8 0xdf803ff9fe03ff2f 0x9f7e00ffe7f80ffc

def z612 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x8c703c3801f00710 0xae31c0f0e007c01c

def z613 : W := mkw 0x0010102000000020 0x0000404080000000 0x8030102000000000 0xaa00c04080000000

def z614 : W := mkw 0x0470d0e287758c64 0xb411c3438a1dd631 0xccf1d3e78ffd9cff 0xff33c74f9e3ff673

def z615 : W := mkw 0x0a80090148004001 0x002a002405200100 0x4c000c0180006000 0x0130003006000180

def z616 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc303c018073e027 0x8f30c0f00601cf80

def z617 : W := mkw 0x246d041c0000001a 0x0091b41070000000 0x204e001800000000 0x0081380060000000

def z618 : W := mkw 0x0010102000108420 0x1000404080004210 0x8070303801f38737 0xae01c0c0e007ce1c

def z619 : W := mkw 0x0470d4b28574a674 0x9411c352ca15d299 0x0071c03e01fc07d0 0x6001c700f807f01f

def z620 : W := mkw 0x0000004002010800 0x2000000100080420 0x008003c00e001808 0x1002000f00380060

def z621 : W := mkw 0x3ffdffbfcd64003f 0xc0fff7feff359000 0xefffffff8e700004 0xffbffffffe39c000

def z622 : W := mkw 0x0000004002010800 0x2000000100080420 0x000013c000019820 0x8000004f00000660

def z623 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x4c803fc18e03f824 0x893200ff06380fe0

def z624 : W := mkw 0x0010d0a204348464 0x940043428810d211 0x8031c226007c1cf9 0xf200c7089801f073

def z625 : W := mkw 0x2ff9bff35a035837 0x20bfe6ffcd680d60 0xdfb1ffc1fe03f82f 0x9f7ec7ff07f80fe0

def z626 : W := mkw 0x0100220010021000 0x0004008800400840 0x1300200070020002 0x044c008001c00800

def z627 : W := mkw 0x1eeb40016cac0001 0xc07bad0005b2b000 0xbfffc0007e0c0008 0x7effff0001f83000

def z628 : W := mkw 0x2ffdffff5e37dc7f 0xb4bff7fffd78df71 0xfffffffffe7ffcff 0xfffffffffff9fff3

def z629 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f002c01fe03f82f 0x057c00b007f80fe0

def z630 : W := mkw 0x01103f701213fe30 0x300440fdc0484ff8 0x00003ff80003ff20 0x800000ffe0000ffc

def z631 : W := mkw 0x2ffdbfff4a01483f 0x20bff6fffd280520 0xefffffff8e01e004 0xffbffffffe380780

def z632 : W := mkw 0x0006000c20880188 0x0800180030822006 0x204e001801800300 0x008138006006000c

def z633 : W := mkw 0x0100220000000000 0x0004008800000000 0x8300220000000000 0x960c008800000000

def z634 : W := mkw 0x0ee00001c9400001 0x003b800007250000 0xdff00001fff0001f 0x3f7fc00007ffc000

def z635 : W := mkw 0x0ee9000148000001 0x003ba40005200000 0xffffc001fe00000f 0x7fffff0007f80000

def z636 : W := mkw 0x0460041081402210 0x0011801042050088 0x4c000c0180006000 0x0130003006000180

def z637 : W := mkw 0x0114f2ee16379dec 0xbc0453cbb858de77 0x80b1f3fe0e7f9ffd 0xfa02c7cff839fe7f

def z638 : W := mkw 0x1eeb0411e9c82211 0x407bac1047a72088 0x7f4e2c19f1826302 0x05fd38b067c6098c

def z639 : W := mkw 0x2fffbfbe208801be 0x08bffefef8822006 0xaffffffe018c07d0 0xfebffffff806301f

def z640 : W := mkw 0x0002000020880000 0x0000080000822000 0xb34e2038718e073b 0xf6cd3880e1c6381c

def z641 : W := mkw 0x2ffdbffe1203583e 0x20bff6fff8480d60 0xaffffffe0003f820 0xfebffffff8000fe0

def z642 : W := mkw 0x0010102000108420 0x1000404080004210 0x0030100000718004 0x0800c0400001c600

def z643 : W := mkw 0x0470102081508420 0x1011c04082054210 0xcc70102181f18437 0xaf31c0408607c610

def z644 : W := mkw 0x0a80000148000001 0x002a000005200000 0x4c8000018e000004 0x0932000006380000

def z645 : W := mkw 0x0460041081402210 0x0011801042050088 0x0040001801800300 0x000100006006000c

def z646 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0xb3cfc0007f8c001b 0x76cf3f0001fe3000

def z647 : W := mkw 0x000200417a8b5981 0x2800080105ea2d66 0x50000001ff8fffff 0x0140000007fe3fff

def z648 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x000013e60e7d9cfd 0x8000004f9839f673

def z649 : W := mkw 0x0a8009414a014801 0x202a002505280520 0x008001c00e000000 0x0002000700380000

def z650 : W := mkw 0x1ef95431cd74a631 0xd07be550c735d298 0xccf1fc398ff3e737 0xaf33c7f0e63fcf9c

def z651 : W := mkw 0x2b8fab8e308a118e 0x08ae3eae38c22846 0x338fc3c6700c18c8 0x50ce3f0f19c03063

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000018003e027 0x0100000006000f80

def z653 : W := mkw 0x3b8feb8f6cac000f 0xc0ee3fae3db2b000 0x338fc3c67e0c0008 0x50ce3f0f19f83000

def z654 : W := mkw 0x14725431edfca631 0xd051c950c7b7f298 0xdc703c39ffffe73f 0xaf71c0f0e7ffff9c

def z655 : W := mkw 0x0470143000000030 0x0011c050c0000000 0x0070003800000000 0x2001c000e0000000

def z656 : W := mkw 0x2ffffffe36bf9dfe 0xbcbffffff8dafe77 0xbffffffe7fff9fff 0xfefffffff9fffe7f

def z657 : W := mkw 0x0002000020880000 0x0000080000822000 0x330e0000700c0008 0x50cc380001c03000

def z658 : W := mkw 0x0b802b0000000000 0x002e00ac00000000 0x0f002c0000000000 0x043c00b000000000

def z659 : W := mkw 0x0106620c34ae1188 0x8804198830d2b846 0xb3ffe23e7ffe1fff 0xfecfff88f9fff87f

def z660 : W := mkw 0x0b90fbe35e37dc65 0xb42e43ef8d78df71 0x93b1d3e67e7d9cfd 0xfa4ec74f99f9f673

def z661 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x0031d3e6007d9cf0 0xe000c74f9801f673

def z662 : W := mkw 0x1a824001edec0001 0xc06a090007b7b000 0xdf800001fffc001f 0x1f7e000007fff000

def z663 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c301c0181f3e737 0x0930c0700607cf9c

def z664 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x538003c1fe03f82f 0x114e000f07f80fe0

def z665 : W := mkw 0x2b94bfbe0000003e 0x00ae52fef8000000 0x8f803ffe00000000 0x9e3e00fff8000000

def z666 : W := mkw 0x0002000020880000 0x0000080000822000 0x204e0000018c0010 0x6081380000063000

def z667 : W := mkw 0x0b822b417a8b5981 0x282e08ad05ea2d66 0xdf803fc1ff8fffff 0x9f7e00ff07fe3fff

def z668 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc301c218071e435 0xab30c0708601c790

def z669 : W := mkw 0x000000415a035801 0x2000000105680d60 0x100000007e001808 0x0040000001f80060

def z670 : W := mkw 0x1efbd0a3edec0025 0xc07bef428fb7b000 0xffffd3e7fffc001f 0xffffff4f9ffff000

def z671 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x938023c07e02182b 0x964e008f01f80860

def z672 : W := mkw 0x0a80090000000000 0x002a002400000000 0x0c801dc000000000 0x0832007700000000

def z673 : W := mkw 0x0114f2ee06358c6c 0xb40453cbb818d631 0xa3fff3fe0e7d9cfd 0xfe8fffcff839f673

def z674 : W := mkw 0x00020000b1dab780 0x1800080002c76ade 0x50000001f1ffffff 0x0140000007c7ffff

def z675 : W := mkw 0x0460041081402210 0x0011801042050088 0xcc402c3981826733 0xa73100b0e606099c

def z676 : W := mkw 0x0574363c8150a638 0x1015d0d8f2054298 0xef7e3e3f81f3e737 0xffbdf8f8fe07cf9c

def z677 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x8070103801f18735 0xaa01c040e007c61c

def z678 : W := mkw 0x2ffdffbe0424003e 0x80bff7fef8109000 0xaffffffe0e7c001d 0xfebffffff839f000

def z679 : W := mkw 0x0b90bbe35a035825 0x202e42ef8d680d60 0xdfb1ffe7fe03f82f 0xff7ec7ff9ff80fe0

def z680 : W := mkw 0x10020001e9c80001 0x4040080007a72000 0x50000001f1800002 0x0140000007c60000

def z681 : W := mkw 0x0a8000414a010801 0x202a000105280420 0xdf8013c1fe01982f 0x9f7e004f07f80660

def z682 : W := mkw 0x0b862b0d788a5189 0x082e18ac35e22946 0xff4e2e3ff18e7ffb 0xf7fd38b8ffc639ff

def z683 : W := mkw 0x0ff03f715a035831 0x203fc0fdc5680d60 0xdff03ff9fe03f82f 0xbf7fc0ffe7f80fe0

def z684 : W := mkw 0x1efbd0e3effd8c65 0xf47bef438fbff631 0xffffd1c1fffd801f 0x7fffff4707fff600

def z685 : W := mkw 0x0469000000000000 0x0011a40000000000 0x207fc00000000000 0x6081ff0000000000

def z686 : W := mkw 0x146b4001edec0001 0xc051ad0007b7b000 0x707fc001fffc001f 0x61c1ff0007fff000

def z687 : W := mkw 0x0b802b0010021000 0x002e00ac00400840 0x9f803fc07002182b 0x9e7e00ff01c00860

def z688 : W := mkw 0x01002b0010025000 0x000400ac00400940 0x00002c0000026000 0x000000b000000980

def z689 : W := mkw 0x0576f6feb7ffbffc 0xbc15dbdbfadffeff 0xffffffffffffffff 0xffffffffffffffff

def z690 : W := mkw 0x0010102000108420 0x1000404080004210 0xcc303c218073e437 0xaf30c0f08601cf90

def z691 : W := mkw 0x0576363c308a11b8 0x0815d8d8f0c22846 0xbf7e3e3e718e1ffb 0xfefdf8f8f9c6387f

def z692 : W := mkw 0x0004000c00000188 0x0800100030000006 0x0000003e000007c0 0x00000000f800001f

def z693 : W := mkw 0x1ffb7f71fffffe31 0xf07fedfdc7fffff8 0xfffffff9ffffff3f 0xffffffffe7fffffc

def z694 : W := mkw 0x3effd4bfedec003f 0xc0fbff52ffb7b000 0xffffc03ffffc001f 0x7fffff00fffff000

def z695 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x330e000070000000 0x00cc380001c00000

def z696 : W := mkw 0x2fffbfbe308a11be 0x08bffefef8c22846 0xbffffffe71820302 0xfefffffff9c6080c

def z697 : W := mkw 0x1a8b000168880001 0x406a2c0005a22000 0x330e000070000000 0x00cc380001c00000

def z698 : W := mkw 0x3efbddb3edec0037 0xc0fbef76cfb7b000 0xffffddc1fffc001f 0x7fffff7707fff000

def z699 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x0081d3e60e0d9ce8 0xd002074f98383673

def z700 : W := mkw 0x2114bfbe0000003e 0x008452fef8000000 0xa34e3ffe00000000 0xf68d38fff8000000

def z701 : W := mkw 0x0000000158025001 0x0000000005600940 0x50000001f0026002 0x0140000007c00980

def z702 : W := mkw 0x0106624c36bf9dc8 0xbc04198930dafe77 0xb34e223e7fff9fff 0xf6cd3888f9fffe7f

def z703 : W := mkw 0x0460000081400000 0x0011800002050000 0xcc703c0181f3e037 0xaf31c0f00607cf80

def z704 : W := mkw 0x04701471db53fe31 0x3011c051c76d4ff8 0xdc703c39fff3ff3f 0xaf71c0f0e7ffcffc

def z705 : W := mkw 0x1eeb4041ffef5801 0xe07bad0107ffbd60 0xffffc001fffff83f 0x7fffff0007ffffe0

def z706 : W := mkw 0x247d94be8150a63e 0x1091f652fa054298 0xec7ffc3f81f3e737 0xefb1fff0fe07cf9c

def z707 : W := mkw 0x2ffdbfbfc950a63f 0x10bff6feff254298 0xfffffffffff3e73f 0xffffffffffffcf9c

def z708 : W := mkw 0x2b9dbfbe0000003e 0x00ae76fef8000000 0xaf8ffffe00000000 0xdebe3ffff8000000

def z709 : W := mkw 0x2ffdbfbe8140003e 0x00bff6fefa050000 0xefffffff81800002 0xffbffffffe060000

def z710 : W := mkw 0x0010d0a204240024 0x8000434288109000 0x80b1d3e60e7c1cfd 0xfa02c74f9839f073

def z711 : W := mkw 0x0a8009415a035801 0x202a002505680d60 0x5c801dc1fe01f80c 0x0972007707f807e0

def z712 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c703c3981f3e716 0x2d31c0f0e607cf9c

def z713 : W := mkw 0x1efb90e3ebd98c65 0x747bee438faf6631 0x7f4e13e7f1819ce2 0x85fd384f9fc60673

def z714 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e223e718e1ffb 0x84cd3888f9c6387f

def z715 : W := mkw 0x1b8f6b4d7eaf5989 0xe86e3dad35fabd66 0x338fc3c67e0c18c8 0x50ce3f0f19f83063

def z716 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5c803fc1fe03f82f 0x897200ff07f80fe0

def z717 : W := mkw 0x01062b0c308a1188 0x080418ac30c22846 0xb34e3ffe718e1ffb 0xf6cd38fff9c6387f

def z718 : W := mkw 0x2fedab8e0000000e 0x00bfb6ae38000000 0x23ffc3c600000000 0x708fff0f18000000

def z719 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb37e223e71fe1fff 0xfecdf888f9c7f87f

def z720 : W := mkw 0x0b802b0148000001 0x002e00ac05200000 0xdf803fc1fe03e02f 0x9f7e00ff07f80f80

def z721 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e223e718e1fda 0x74cd3888f9c6387f

def z722 : W := mkw 0x0ef994b200000034 0x003be652c8000000 0xaffffffe00000000 0xfebffffff8000000

def z723 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0x6fbfdfc78071e004 0x59beff7f1e01c780

def z724 : W := mkw 0x0b892b0000000000 0x002e24ac00000000 0x238fc3c000000000 0x508e3f0f00000000

def z725 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xfffffc39ffffe73f 0xfffffff0e7ffff9c

def z726 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff8073e724 0xffbffffffe01cf9c

def z727 : W := mkw 0x2114bffe1213fe3e 0x308452fff8484ff8 0x00003ffe0003ff20 0x800000fff8000ffc

def z728 : W := mkw 0x2b9dbfbe0000003e 0x00ae76fef8000000 0x238fc3fe00000000 0x508e3f0ff8000000

def z729 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fe1fe03fc3f 0xbf7e00ff87f80ff0

def z730 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa38fc3e600000000 0xf28e3f0f98000000

def z731 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc1fe03e006 0x9f7e00ff07f80f80

def z732 : W := mkw 0x0574b6be8150a63c 0x1015d2dafa054298 0xefffffff81f3e737 0xffbffffffe07cf9c

def z733 : W := mkw 0x0ee940014c240001 0x803ba50005309000 0xffffc001fe7c001f 0x7fffff0007f9f000

def z734 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xaffffffe01f20733 0xfebffffff807c81c

def z735 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fbfddc000000000 0x08beff7700000000

def z736 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xff4e223ff18e1fff 0xfffd3888ffc6387f

def z737 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0xacfffffe00000000 0xfeb3fffff8000000

def z738 : W := mkw 0x14725061effd8c61 0xf451c94187bff631 0xdc701021fffd9cff 0xaf71c04087fff673

def z739 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fffc001fffc001c 0x79ffff0007fff000

def z740 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x93b1d3e67e7d9cff 0xfe4ec74f99f9f673

def z741 : W := mkw 0x1fed620ddd661189 0xc87fb58837759846 0x4cb1e23f8e721fe4 0x8932c788fe39c87f

def z742 : W := mkw 0x201d90ae0000002e 0x00807642b8000000 0xa0bfd3e600000000 0xfa82ff4f98000000

def z743 : W := mkw 0x100240417eaf5801 0xe040090105fabd60 0x50000001fe0ff82f 0x0140000007f83fe0

def z744 : W := mkw 0x100240416ebd8c41 0xf440090105baf631 0x100000007e7d9cfd 0x0040000001f9f673

def z745 : W := mkw 0x0114bbee1213ddec 0x3c0452efb8484f77 0x00003ffe0003ffe0 0x800000fff8000fff

def z746 : W := mkw 0x0a8000414a010801 0x202a000105280420 0xdf803fc1fe03f82f 0x9f7e00ff07f80fe0

def z747 : W := mkw 0x247d94be8150a63e 0x1091f652fa054298 0xa0ffd3fe01f18735 0xfa83ff4ff807c61c

def z748 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0x207fd3fe00000000 0xe081ff4ff8000000

def z749 : W := mkw 0x2fedaf9e8140221e 0x00bfb6be7a050088 0x6fcfefdf81826302 0x55bf3fbf7e06098c

def z750 : W := mkw 0x156b6b40b7ef5800 0xe055adad02dfbd60 0x207fffc001fff830 0xe081ffff0007ffe0

def z751 : W := mkw 0x0104a28e0000000c 0x0004128a38000000 0x238fc3c600000000 0x508e3f0f18000000

def z752 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x23cfc3fe00000000 0x708f3f0ff8000000

def z753 : W := mkw 0x0b842b4d5a035809 0x202e10ad35680d60 0xdf803ffffe03f82f 0x9f7e00fffff80fe0

def z754 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0x20ffc3fe00000000 0x7083ff0ff8000000

def z755 : W := mkw 0x0b90fba35c36d465 0x942e43ee8d70db51 0x5f31ec27f07e64d2 0x657cc7b09fc1f993

def z756 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xefffffff8183e737 0xffbffffffe060f9c

def z757 : W := mkw 0x2fedab8e0000000e 0x00bfb6ae38000000 0x2fbfc3c600000000 0x58beff0f18000000

def z758 : W := mkw 0x2b9dbfbe0010a63e 0x10ae76fef8004298 0x238ffffe0003e720 0xd08e3ffff8000f9c

def z759 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fe7fe03f82f 0xff7e00ff9ff80fe0

def z760 : W := mkw 0x247d94ff5a03583f 0x2091f653fd680d60 0x707fc03ffe03f82f 0x61c1ff00fff80fe0

def z761 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0xafffdfe600000000 0xfebfff7f98000000

def z762 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0xffbfc001fe7c001f 0x7ffeff0007f9f000

def z763 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0x2cffddd800000000 0x08b3ff7760000000

def z764 : W := mkw 0x0a89808200000004 0x002a260208000000 0x238fc3c600000000 0x508e3f0f18000000

def z765 : W := mkw 0x147bd4b2a5fca674 0xd451ef52ca97f299 0x207fc03e01fc07d0 0x6081ff00f807f01f

def z766 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703e3981f3ff3f 0xbf31c0f8e607cffc

def z767 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e223e718e1ff2 0xe4cd3888f9c6387f

def z768 : W := mkw 0x0104624c06358c48 0xb40411893018d631 0xa34e223e0e7d9cfd 0xf68d3888f839f673

def z769 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c403c3981f3e737 0x853100f0e607cf9c

def z770 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2cfffffe00000000 0xe8b3fffff8000000

def z771 : W := mkw 0x14725471fffffe31 0xf051c951c7fffff8 0xdc703c39ffffff3f 0xaf71c0f0e7fffffc

def z772 : W := mkw 0x0ffdb2ae0000002c 0x003ff6cab8000000 0xaffff3fe00000000 0xfebfffcff8000000

def z773 : W := mkw 0x247d9dbe0000003e 0x0091f676f8000000 0x207fddfe00000000 0x6081ff77f8000000

def z774 : W := mkw 0x0460c4d287652a54 0xa41183134a1d94a9 0x4cc1efdf8f8e7bca 0x553307bf7e3e39ef

def z775 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fcffffe00000000 0xd4bf3ffff8000000

def z776 : W := mkw 0x1fef2b0df9ca5189 0x487fbcac37e72946 0x7f4e2c19f1826302 0x05fd38b067c6098c

def z777 : W := mkw 0x347fd4bea5fca63e 0xd0d1ff52fa97f298 0x207fc03e01fc0710 0x6081ff00f807f01c

def z778 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c3981f3e306 0xaf31c0f0e607cf8c

def z779 : W := mkw 0x2ffdbfbe1012b7be 0x18bff6fef8404ade 0xaffffffe0003ffe0 0xfebffffff8000fff

def z780 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0x2cbfddc600000000 0x48b2ff7718000000

def z781 : W := mkw 0x1a9b54316cbca631 0xd06a6d50c5b2f298 0x338ffc387e0fe728 0xd0ce3ff0e1f83f9c

def z782 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c703c1981f3e737 0x0d31c0f06607cf9c

def z783 : W := mkw 0x2b9dbbae0000002e 0x00ae76eeb8000000 0x238fd3e600000000 0xd08e3f4f98000000

def z784 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xef8fffc78003e027 0xdfbe3fff1e000f80

def z785 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f803fc1fe03f80e 0x1d7e00ff07f80fe0

def z786 : W := mkw 0x1eeb4411edec2211 0xc07bad1047b7b088 0xffffcc01fffc601f 0x7fffff3007fff180

def z787 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb3ce33fe718e1ffb 0xfecf38cff9c6387f

def z788 : W := mkw 0x2ffdbfbfd952f63f 0x10bff6feff654bd8 0xfffffffff1f3e737 0xffffffffffc7cf9c

def z789 : W := mkw 0x2fed6f5c06358c5a 0xb4bfb5bd7018d631 0x2f4e2c180e7d9cfd 0x04bd38b06039f673

def z790 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x80b1c3e60e7c1cfd 0xfa02c70f9839f073

def z791 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0xa3ffd3e60e7d9cfd 0xfe8fff4f9839f673

def z792 : W := mkw 0x14624041ffef5801 0xe051890107ffbd60 0xdc703c01fffff83f 0xaf71c0f007ffffe0

def z793 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3e60e7d9cf8 0xf002c74f9839f673

def z794 : W := mkw 0x247d94be0000003e 0x0091f652f8000000 0x20ffd1fe00000000 0x6883ff47f8000000

def z795 : W := mkw 0x3116ffbfedec003f 0xc0c45bfeffb7b000 0x50003ffffffc001f 0x814000fffffff000

def z796 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xafffc3fe00000000 0x7ebfff0ff8000000

def z797 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80f1d3e60ffd9cff 0xfe03c74f983ff673

def z798 : W := mkw 0x0a8009415a035801 0x202a002505680d60 0xdc803dc1fe03f82f 0x8f7200f707f80fe0

def z799 : W := mkw 0x047990a200000024 0x0011e64288000000 0xa0ffd3e600000000 0xfa83ff4f98000000

def z800 : W := mkw 0x0a9990a200000024 0x002a664288000000 0xa3bfd3e600000000 0xfa8eff4f98000000

def z801 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc021fffc043f 0xffffff0087fff010

def z802 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc227fffc001f 0xffffff089ffff000

def z803 : W := mkw 0x2ffdbfbf4800003f 0x00bff6fefd200000 0xfffffffff0000002 0xffffffffffc00000

def z804 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e023e718e1ffb 0x70cd3808f9c6387f

def z805 : W := mkw 0x0b892b415a035801 0x202e24ad05680d60 0xff8fffc1fe03f82f 0xdffe3fff07f80fe0

def z806 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe000c18c8 0xfebffffff8003063

def z807 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc039fffc071f 0x7fffff00e7fff01c

def z808 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80f1f3fe0e7d9cfd 0xfe03c7cff839f673

def z809 : W := mkw 0x2ffdbfbe0010a63e 0x10bff6fef8004298 0xaffffffe0183e733 0xfebffffff8060f9c

def z810 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803dc1fe03e027 0x8f7e00f707f80f80

def z811 : W := mkw 0x0b842b4d5a035809 0x202e10ad35680d60 0xffce3fd9fe03f82f 0x9fff38ff67f80fe0

def z812 : W := mkw 0x0116f2ee36bf9dec 0xbc045bcbb8dafe77 0x33fff1d87ff38306 0x0ccfffc761ffce0c

def z813 : W := mkw 0x2114bffe1213dc7e 0x348452fff8484f71 0x00003ffe0003fce0 0x800000fff8000ff3

def z814 : W := mkw 0x2ffdbfbe0000223e 0x00bff6fef8000088 0xaffffffe00026300 0xfebffffff800098c

def z815 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xeffffdf981f3e737 0xafbffff7e607cf9c

def z816 : W := mkw 0x2b8d2b4d5a03580b 0x20ae34ad35680d60 0xff8e3fc1fe03f82f 0x9ffe38ff07f80fe0

def z817 : W := mkw 0x2b9dbbae0000002e 0x00ae76eeb8000000 0xafbfffe600000000 0xfebeffff98000000

def z818 : W := mkw 0x0a86094d6a894989 0x282a182535aa2526 0x6cce1dff8f8de7d4 0x69b33877fe3e379f

def z819 : W := mkw 0x3ffdbfbfc940003f 0x40fff6feff250000 0xefffffff80000000 0xffbffffffe000000

def z820 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc1fe01f80c 0x9f7e00ff07f807e0

def z821 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fe7fe03fcef 0x9f7e00ff9ff80ff3

def z822 : W := mkw 0x0104620c14261188 0x8804118830509846 0x80b1e23e0e7e1ffd 0xfa02c788f839f87f

def z823 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2f7ffffe00000000 0xe4bdfffff8000000

def z824 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f803fc1fe03f82c 0x997e00ff07f80fe0

def z825 : W := mkw 0x2ffdbfbe0010847e 0x14bff6fef8004211 0xaffffffe000004c0 0xfebffffff8000013

def z826 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fffeffe00000000 0x74bfffbff8000000

def z827 : W := mkw 0x2fed2f1c0000001a 0x00bfb4bc70000000 0xafffffd800000000 0xfebfffff60000000

def z828 : W := mkw 0x257dbfbe0000003e 0x0095f6fef8000000 0xa37ffffe00000000 0xf68dfffff8000000

def z829 : W := mkw 0x0eeb400024ac0000 0x803bad000092b000 0xbfffc0007ffc001f 0x7effff0001fff000

def z830 : W := mkw 0x2b9dbbae0000002e 0x00ae76eeb8000000 0x23bfc3e600000000 0x708eff0f98000000

def z831 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fffdffe00000000 0x78bfff7ff8000000

def z832 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xbf4e3e3e718e1ffb 0xfefd38f8f9c6387f

def z833 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001ffffe03f 0x7fffff0007ffff80

def z834 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffbfc001fe7c000f 0x5ffeff0007f9f000

def z835 : W := mkw 0x001290a2308a11a4 0x08004a4288c22846 0x90b1d3e6718e1ffb 0xfa42c74f99c6387f

def z836 : W := mkw 0x2ffdbfbe100211be 0x08bff6fef8400846 0xaffffffe000018c0 0xfebffffff8000063

def z837 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0xccf1ffff8fffffff 0xff33c7fffe3fffff

def z838 : W := mkw 0x0ee900415a035801 0x203ba40105680d60 0xffffc001fe03f82f 0x7fffff0007f80fe0

def z839 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2ffffffe00000000 0x8cbffffff8000000

def z840 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xaffffffe00700000 0xfebffffff801c000

def z841 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffd001fffd803f 0xffffff4007fff600

def z842 : W := mkw 0x2ffdbbae0000002e 0x00bff6eeb8000000 0xafffd3e600000000 0xfebfff4f98000000

def z843 : W := mkw 0x200d808e0000000e 0x0080360238000000 0x208fc3c600000000 0x50823f0f18000000

def z844 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3e60e7d9cdc 0x7802c74f9839f673

def z845 : W := mkw 0x001490ae0000002c 0x00005242b8000000 0xa0ffd3fe00000000 0xfa83ff4ff8000000

def z846 : W := mkw 0x2efb9db2308a11b6 0x08bbee76c8c22846 0x1cb1ddc0718e1ffb 0x0872c77701c6387f

def z847 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffdd800000000 0x7ebffff760000000

def z848 : W := mkw 0x2ffdbfbe8140223e 0x00bff6fefa050088 0xefffffff8183e327 0xffbffffffe060f8c

def z849 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e3e3e718ffffb 0xf6cd38f8f9c63fff

def z850 : W := mkw 0x2ffdbfbe8140223e 0x00bff6fefa050088 0xefffffff81826733 0xffbffffffe06099c

def z851 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa3cfc3c600000000 0x768f3f0f18000000

def z852 : W := mkw 0x257db6be0000003e 0x0095f6daf8000000 0xa3fff3fe00000000 0xfe8fffcff8000000

def z853 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x23bfc3c600000000 0x508eff0f18000000

def z854 : W := mkw 0x0010d0e206250864 0xa400434388189421 0x80b1d3e60e7c18dd 0xfa02c74f9839f063

def z855 : W := mkw 0x100240417eaf5801 0xe040090105fabd60 0x100000007e0c1808 0x0040000001f83060

def z856 : W := mkw 0x2efd9dbe8150a63e 0x10bbf676fa054298 0xecfffdff81f3e737 0xefb3fff7fe07cf9c

def z857 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xfffffc01fffc001f 0xfffffff007fff000

def z858 : W := mkw 0x2ffdbfbe0010a63e 0x10bff6fef8004298 0xefffffff8003e727 0xffbffffffe000f9c

def z859 : W := mkw 0x1eeb4001edec2201 0xc07bad0007b7b088 0xffffc001fffe631f 0x7fffff0007fff98c

def z860 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0x33bfc0007e7c0018 0x70ceff0001f9f000

def z861 : W := mkw 0x0b842b4d5a035809 0x202e10ad35680d60 0xffce3ffffe0ffcff 0xffff38fffff83ff3

def z862 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2ffffdfe00000000 0x6cbffff7f8000000

def z863 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe01800013 0xfebffffff8060000

def z864 : W := mkw 0x2b8dab8e8150a60e 0x10ae36ae3a054298 0x638fc3c781f3e737 0x518e3f0f1e07cf9c

def z865 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xaffffffe007d9cfd 0xfebffffff801f673

def z866 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f803fc1fe03f826 0x8d7e00ff07f80fe0

def z867 : W := mkw 0x00024040b7ffbfc0 0xbc00090102dffeff 0x50000001ffffffff 0x0140000007ffffff

def z868 : W := mkw 0x0ff03f71db53fe31 0x303fc0fdc76d4ff8 0x13f003f87ff01f18 0x304fc00fe1ffc07c

def z869 : W := mkw 0x257dbfbe8150a63e 0x1095f6fefa054298 0xec7fffff81f3e737 0xefb1fffffe07cf9c

def z870 : W := mkw 0x0476d4bea5fca7fc 0x9c11db52fa97f29f 0x207fc03e01fc07d0 0x6081ff00f807f01f

def z871 : W := mkw 0x14725471effdae71 0xf451c951c7bff6b9 0xdc703c39ffffffff 0xaf71c0f0e7ffffff

def z872 : W := mkw 0x2ffdbfbe0010a63e 0x10bff6fef8004298 0xaffffffe0073e735 0xfebffffff801cf9c

def z873 : W := mkw 0x2ffdbfbf4800003f 0x00bff6fefd200000 0xbffffffe7e000008 0xfefffffff9f80000

def z874 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffd3c1fffc001f 0xffffff4f07fff000

def z875 : W := mkw 0x2b8dab8f5802500f 0x00ae36ae3d600940 0x7f8fefc7f0026002 0x55fe3fbf1fc00980

def z876 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xaf8fc3c600000000 0x5ebe3f0f18000000

def z877 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe000c0019 0xfebffffff8003000

def z878 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xaffffffe00018420 0xfebffffff8000610

def z879 : W := mkw 0x0010d4f20635ae74 0xb4004353c818d6b9 0xccb1ffff8e7fffff 0xff32c7fffe39ffff

def z880 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e223e718e1fea 0xd4cd3888f9c6387f

def z881 : W := mkw 0x2ffdbfbe8140003e 0x00bff6fefa050000 0xaffffffe01f00010 0xfebffffff807c000

def z882 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x00b1c3c60e7c18d8 0x7002c70f1839f063

def z883 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xff4e2e3ff18e7ffb 0xf7fd38b8ffc639ff

def z884 : W := mkw 0x146b4000a5ec0000 0xc051ad000297b000 0xb3ffc0007ffc001f 0x7ecfff0001fff000

def z885 : W := mkw 0x146b4001edec0001 0xc051ad0007b7b000 0xf37fc001fffc001f 0x77cdff0007fff000

def z886 : W := mkw 0x0ff93f3000000030 0x003fe4fcc0000000 0xaffffff800000000 0xfebfffffe0000000

def z887 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xaffffffe00718004 0xfebffffff801c600

def z888 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1c3e60e7c1cf9 0xf202c70f9839f073

def z889 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xaffffffe00700410 0xfebffffff801c010

def z890 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xf34e223ff18fffff 0xf7cd3888ffc63fff

def z891 : W := mkw 0x0104a28e0000000c 0x0004128a38000000 0xa3cfe3fe00000000 0xf68f3f8ff8000000

def z892 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3e60e7d9cf4 0xe802c74f9839f673

def z893 : W := mkw 0x1eeb4901edec0001 0xc07bad2407b7b000 0xffffddc1fffc001f 0x7fffff7707fff000

def z894 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x238fc3c6000c18c8 0x508e3f0f18003063

def z895 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80f1d3fe0ffd9ffd 0xfa03c74ff83ff67f

def z896 : W := mkw 0x0ee9808200000004 0x003ba60208000000 0xafffc3c600000000 0x7ebfff0f18000000

def z897 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfb03fc1fe73f83f 0xbf7ec0ff07f9cfe0

def z898 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x2f8fefc600000000 0x54be3fbf18000000

def z899 : W := mkw 0x01002b415a035801 0x200400ad05680d60 0xdc003fc1fe03f82f 0x8f7000ff07f80fe0

def z900 : W := mkw 0x2b8dab8f4800000f 0x00ae36ae3d200000 0xff8fc3c7fe00000f 0x5ffe3f0f1ff80000

def z901 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xccf1fc3981f3e737 0xff33c7f0e607cf9c

def z902 : W := mkw 0x0ef990a281508424 0x103be6428a054210 0xefffd3e781f18437 0xffbfff4f9e07c610

def z903 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fe7c000c 0x7fffff0007f9f000

def z904 : W := mkw 0x0002400024ac0000 0x800009000092b000 0xb3bfc0007e7c001d 0x7aceff0001f9f000

def z905 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x2f8fdfc600000000 0x58be3f7f18000000

def z906 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xefffffff80000007 0xffbffffffe000000

def z907 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x73ffc001fffc001f 0x71cfff0007fff000

def z908 : W := mkw 0x2b8dab8e1002100e 0x00ae36ae38400840 0x338fc3c670001808 0x50ce3f0f19c00060

def z909 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1c3c60e7c18c8 0x5002c70f1839f063

def z910 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e223e718e1ff8 0xf0cd3888f9c6387f

def z911 : W := mkw 0x2ffdbfbfc940003f 0x00bff6feff250000 0xfffffffffff0001f 0xffffffffffffc000

def z912 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc207fffc18df 0x7fffff081ffff063

def z913 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fffc1cff 0x7fffff0007fff073

def z914 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0x2fcfedd800000000 0x04bf3fb760000000

def z915 : W := mkw 0x1ee94001cd640001 0xc07ba50007359000 0xffffc001fe70000f 0x7fffff0007f9c000

def z916 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xccf03ff981f3e737 0xbf33c0ffe607cf9c

def z917 : W := mkw 0x0576363cb1dab7b8 0x1815d8d8f2c76ade 0x7f3e1e07f07df8cc 0x59fcf8781fc1f7e3

def z918 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c3981ffffff 0xaf31c0f0e607ffff

def z919 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xef7e3c3981f3e737 0xffbdf8f0e607cf9c

def z920 : W := mkw 0x2ffdbfbe8150843e 0x10bff6fefa054210 0xefffffff81f18437 0xffbffffffe07c610

def z921 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c703c3981f3e734 0xa931c0f0e607cf9c

def z922 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x238fe3fe00000000 0xd08e3f8ff8000000

def z923 : W := mkw 0x1eeb4411edec2211 0xc07bad1047b7b088 0xffffec39fffe673f 0xffffffb0e7fff99c

def z924 : W := mkw 0x0a8009415a035801 0x202a002505680d60 0xdf801dc1fe03f82f 0x1f7e007707f80fe0

def z925 : W := mkw 0x2ef99db28150a636 0x10bbe676ca054298 0xeffffdf981f3e737 0xffbffff7e607cf9c

def z926 : W := mkw 0x257dbfbe8150a63e 0x1095f6fefa054298 0x207ffffe01f3e730 0xe081fffff807cf9c

def z927 : W := mkw 0x2fedab8e0000000e 0x00bfb6ae38000000 0x2fcfc3c600000000 0x54bf3f0f18000000

def z928 : W := mkw 0x2b8dab8e1002118e 0x08ae36ae38400846 0x238fc3c6000018c0 0x508e3f0f18000063

def z929 : W := mkw 0x2ffdbfbe8140003e 0x00bff6fefa050000 0xefffffff80700004 0xffbffffffe01c000

def z930 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xbfffc0007ffc0018 0x7effff0001fff000

def z931 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xa3ffe3fe00000000 0xf68fff8ff8000000

def z932 : W := mkw 0x2ff9bfb200000036 0x00bfe6fec8000000 0xafffffc000000000 0xfebfffff00000000

def z933 : W := mkw 0x046004108150a610 0x1011801042054298 0x4c402c1981f3e306 0x053100b06607cf8c

def z934 : W := mkw 0x0a8009414a014801 0x202a002505280520 0xdf801fc1fe01f82f 0x9f7e007f07f807e0

def z935 : W := mkw 0x2ffdbfbf5802503f 0x00bff6fefd600940 0xbffffffe70000000 0xfefffffff9c00000

def z936 : W := mkw 0x0b842b4d5a035809 0x202e10ad35680d60 0xffce3fffff83ff3f 0xffff38fffffe0ffc

def z937 : W := mkw 0x2b9dbbae0000002e 0x00ae76eeb8000000 0xa3fff3fe00000000 0xfe8fffcff8000000

def z938 : W := mkw 0x0010102000108420 0x1000404080004210 0xcc703c3981f3e737 0xaf31c0f0e607cf9c

def z939 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0xaffffdf800000000 0xfebffff7e0000000

def z940 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1c3e60e7c1cdd 0x7a02c70f9839f073

def z941 : W := mkw 0x2ffdbfbe8140223e 0x00bff6fefa050088 0xefffffff80006000 0xffbffffffe000180

def z942 : W := mkw 0x0a8009415a035801 0x202a002505680d60 0xdc801fc1fe03f82f 0x9b72007f07f80fe0

def z943 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffe039fffc001f 0xffffff80e7fff000

def z944 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c3f81ffe7f7 0xef31c0f0fe07ff9f

def z945 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81f1e017 0xffbffffffe07c780

def z946 : W := mkw 0x0010d4f206358c74 0xb4004353c818d631 0x80b1fffe0e7d9cfd 0xfa02c7fff839f673

def z947 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffe001fffe003f 0xffffff8007fff800

def z948 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fffe073f 0x7fffff0007fff81c

def z949 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x00b1c3c60e7c18cc 0x5802c70f1839f063

def z950 : W := mkw 0x2ffdbfbe100211be 0x08bff6fef8400846 0xbffffffe70021feb 0xfefffffff9c0087f

def z951 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb3ce223e7f8e1fff 0xfecf3888f9fe387f

def z952 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f003fc1fe03f82f 0x857c00ff07f80fe0

def z953 : W := mkw 0x100240416ead0841 0xe440090105bab421 0x100000007e0c18c8 0x0040000001f83063

def z954 : W := mkw 0x0010d4f20635ae74 0xb4004353c818d6b9 0x80b1dfe60e7dfcfd 0xfa02c77f9839f7f3

def z955 : W := mkw 0x04624000a5ec0000 0x801189000297b000 0xffffc001fffc001f 0x7fffff0007fff000

def z956 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xafbfdfe600000000 0xfabeff7f98000000

def z957 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf801fc1fe01f80f 0x1f7e007f07f807e0

def z958 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xffce3fc1fe03f82f 0xffff38ff07f80fe0

def z959 : W := mkw 0x2114bfbe0000003e 0x008452fef8000000 0xa3fffffe00000000 0xfe8ffffff8000000

def z960 : W := mkw 0x0ee90001c9400001 0x003ba40007250000 0xffffc001fff0001f 0x7fffff0007ffc000

def z961 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fffc001fffc001f 0x0dffff0007fff000

def z962 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f801fc1fe03f82f 0x197e007f07f80fe0

def z963 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fff00006 0x7fffff0007ffc000

def z964 : W := mkw 0x211dbfbe0000003e 0x008476fef8000000 0x200ffffe00000000 0xc0803ffff8000000

def z965 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffdf800000000 0xaebffff7e0000000

def z966 : W := mkw 0x2114bffe12139dfe 0x3c8452fff8484e77 0x00003ffe00039fe0 0x800000fff8000e7f

def z967 : W := mkw 0x1eeb4411edec2211 0xc07bad1047b7b088 0xfffffc19ffffe33f 0xfffffff067ffff8c

def z968 : W := mkw 0x2b8dab8f4800000f 0x00ae36ae3d200000 0x338fc3c67e000008 0x50ce3f0f19f80000

def z969 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c1981f3e327 0x8f31c0f06607cf8c

def z970 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0xacffdffe00000000 0xfab3ff7ff8000000

def z971 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fffc001fffc0016 0x6dffff0007fff000

def z972 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe0e00000d 0xfebffffff8380000

def z973 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00001ce0 0xfebffffff8000073

def z974 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xb3ffc0007ffc001d 0x7acfff0001fff000

def z975 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e023e718c1fdb 0x76cd3808f9c6307f

def z976 : W := mkw 0x2fedab8e0000000e 0x00bfb6ae38000000 0xafffe3fe00000000 0xfebfff8ff8000000

def z977 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc027fffc04df 0x7fffff009ffff013

def z978 : W := mkw 0x046004108150a610 0x1011801042054298 0xcc402c3981f3e737 0xa73100b0e607cf9c

def z979 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf801fc1fe01f82d 0x9b7e007f07f807e0

def z980 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3e60e7d9cfd 0x8802c74f9839f673

def z981 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fff00017 0x2fffff0007ffc000

def z982 : W := mkw 0x0000c0c206358c44 0xb40003030818d631 0x80b1c3c60e7d9cfd 0x7a02c70f1839f673

def z983 : W := mkw 0x046004108150a610 0x1011801042054298 0xcc702c1981f3e737 0x2f31c0b06607cf9c

def z984 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xefffffff8001e004 0xffbffffffe000780

def z985 : W := mkw 0x0574b6be0000003c 0x0015d2daf8000000 0xaffffffe00000000 0xfebffffff8000000

def z986 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fbffffe00000000 0xd8befffff8000000

def z987 : W := mkw 0x2b9dbfbe0000003e 0x00ae76fef8000000 0x238fdfc600000000 0x508e3f7f18000000

def z988 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fffc001fffc001a 0x75ffff0007fff000

def z989 : W := mkw 0x10024040a7fd8c40 0xf4400901029ff631 0x000000000ffd9cfd 0x00000000003ff673

def z990 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0x6ffffdd981f3e306 0x0dbffff76607cf8c

def z991 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0xacfffdfe00000000 0xeeb3fff7f8000000

def z992 : W := mkw 0x0b94bbae0000002c 0x002e52eeb8000000 0xaffffffe00000000 0xfebffffff8000000

def z993 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0x334e203e718e1ffb 0x64cd3880f9c6387f

def z994 : W := mkw 0x2b8daf9e0000001e 0x00ae36be78000000 0x238fefde00000000 0x508e3fbf78000000

def z995 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfc03fd9ff83fb2f 0x9f7f00ff67fe0fec

def z996 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0xafcfffde00000000 0xdebf3fff78000000

def z997 : W := mkw 0x0114b2ee12139dec 0x3c0452cbb8484e77 0x000013e600019ce0 0x8000004f98000673

def z998 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa38fe3c600000000 0xd68e3f8f18000000

def z999 : W := mkw 0x2ffdbfbe8140223e 0x00bff6fefa050088 0xaffffffe01800300 0xfebffffff806000c

def z1000 : W := mkw 0x0002000020880000 0x0000080000822000 0xb34e223e718e1ffb 0xf6cd3888f9c6387f

def z1001 : W := mkw 0x1eeb4411edec0011 0xc07bad1047b7b000 0xffffec19fffc001f 0x7fffffb067fff000

def z1002 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0x20ffc1fe00000000 0x6083ff07f8000000

def z1003 : W := mkw 0x257dbfbe0000003e 0x0095f6fef8000000 0xac7ffffe00000000 0xeeb1fffff8000000

def z1004 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0x2cffddc000000000 0x68b3ff7700000000

def z1005 : W := mkw 0x0ee9000000000000 0x003ba40000000000 0xafffd3c000000000 0xfebfff4f00000000

def z1006 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81f3e306 0xffbffffffe07cf8c

def z1007 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1c3e60e7d9cfd 0x7002c70f9839f673

def z1008 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x238fc1c000000000 0x008e3f0700000000

def z1009 : W := mkw 0x1eeb40016cac0001 0xc07bad0005b2b000 0xbfffc0007e7c001d 0x7effff0001f9f000

def z1010 : W := mkw 0x0114b2ae0000002c 0x000452cab8000000 0xa3bfd3e600000000 0xfa8eff4f98000000

def z1011 : W := mkw 0x001090a200000024 0x0000424288000000 0xa3ffd3e600000000 0xfe8fff4f98000000

def z1012 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x23cfe3de00000000 0x548f3f8f78000000

def z1013 : W := mkw 0x047094b28150a634 0x1011c252ca054298 0xcc71fc3f81f3e737 0xef31c7f0fe07cf9c

def z1014 : W := mkw 0x2b8dab8f5802500f 0x00ae36ae3d600940 0x338fc3c670000000 0x50ce3f0f19c00000

def z1015 : W := mkw 0x0ef994b28150a634 0x103be652ca054298 0xefffffff81f3e737 0xffbffffffe07cf9c

def z1016 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc1fe0ffcff 0x9f7e00ff07f83ff3

def z1017 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xfffffffff003f82f 0xffffffffffc00fe0

def z1018 : W := mkw 0x257dbfbe0000003e 0x0095f6fef8000000 0x207fc3fe00000000 0x6081ff0ff8000000

def z1019 : W := mkw 0x2ffdbfbe100211be 0x08bff6fef8400846 0xaffffffe00020300 0xfebffffff800080c

def z1020 : W := mkw 0x0012506036bf9de0 0xbc00494180dafe77 0x907030387fff9fff 0xae41c0c0e1fffe7f

def z1021 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xccf03c398ff3e73f 0xbf33c0f0e63fcf9c

def z1022 : W := mkw 0x2ffdbfbe0010a63e 0x10bff6fef8004298 0xaffffffe0001e000 0xfebffffff8000780

def z1023 : W := mkw 0x0000c0c206250844 0xa400030308189421 0x80b1d3c60e7d98fd 0xfa02c74f1839f663

def z1024 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0x2f8fcfc600000000 0x50be3f3f18000000

def z1025 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1f3e60e7f9cff 0xfe02c7cf9839fe73

def z1026 : W := mkw 0x2efd94be0000003e 0x00bbf652f8000000 0xafffd3fe00000000 0xfebfff4ff8000000

def z1027 : W := mkw 0x0ee9090000000000 0x003ba42400000000 0xafffddc000000000 0x7ebfff7700000000

def z1028 : W := mkw 0x0a8009414a014801 0x202a002505280520 0x5c801dc1fe01e00f 0x0972007707f80780

def z1029 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffbfc001fe7c001d 0x7bfeff0007f9f000

def z1030 : W := mkw 0x047094b28150a634 0x1011c252ca054298 0xcc703fff81f3e737 0xaf31c0fffe07cf9c

def z1031 : W := mkw 0x2ffdbfbe000001be 0x08bff6fef8000006 0xaffffffe000007c0 0xfebffffff800001f

def z1032 : W := mkw 0x0b86ebcf7eaf59cd 0xac2e1baf3dfabd67 0x338fc3c67e0c18c8 0x50ce3f0f19f83063

def z1033 : W := mkw 0x0b842b4d5a035989 0x282e10ad35680d66 0xdf803fd9fe03fb2f 0x9f7e00ff67f80fec

def z1034 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfc03fc1ff83f83f 0xbf7f00ff07fe0fe0

def z1035 : W := mkw 0x0002404026bd8dc0 0xbc000901009af637 0x000000000ffd9ffd 0x00000000003ff67f

def z1036 : W := mkw 0x001014308150a630 0x10004050c2054298 0xcc003c3981f3e737 0x8f3000f0e607cf9c

def z1037 : W := mkw 0x2b9dbbae0010842e 0x10ae76eeb8004210 0xa3bfd3e600718435 0xfa8eff4f9801c610

def z1038 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0x23ffc3fe01f00710 0x708fff0ff807c01c

def z1039 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00018025 0xfebffffff8000600

def z1040 : W := mkw 0x2b9dbfbe0000003e 0x00ae76fef8000000 0xa3bffffe00000000 0xfa8efffff8000000

def z1041 : W := mkw 0x2ffdbfbe1002503e 0x00bff6fef8400940 0xaffffffe00026000 0xfebffffff8000980

def z1042 : W := mkw 0x2b8dab8e1002100e 0x00ae36ae38400840 0xb38fe3c67002182b 0xd6ce3f8f19c00860

def z1043 : W := mkw 0x0006000c308a1188 0x0800180030c22846 0xb34e003e718e1ffb 0x76cd3800f9c6387f

def z1044 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00000431 0xfebffffff8000010

def z1045 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xefffffff80026002 0xffbffffffe000980

def z1046 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3c60e7d98dd 0x7a02c74f1839f663

def z1047 : W := mkw 0x1eeb4001edec0181 0xc87bad0007b7b006 0xffffc001fffc07df 0x7fffff0007fff01f

def z1048 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfc03fffff8fffff 0xff7f00fffffe3fff

def z1049 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xafffdfc600000000 0x7ebfff7f18000000

def z1050 : W := mkw 0x0fe92b0000000000 0x003fa4ac00000000 0xafffc3c000000000 0x7ebfff0f00000000

def z1051 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc7fe0ff8ef 0xdf7e00ff1ff83fe3

def z1052 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffe23ffffe1fff 0xffffff88fffff87f

def z1053 : W := mkw 0x001290e222998c64 0x34004a43888a6631 0xb34e13e6718d9cfb 0xf6cd384f99c63673

def z1054 : W := mkw 0x10024041efed4801 0xe040090107bfb520 0x50000001fffde01f 0x0140000007fff780

def z1055 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe0003e020 0xfebffffff8000f80

def z1056 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0xc0b1d3e78e7ffcff 0xfb02c74f9e39fff3

def z1057 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0x33bfc0007e7c000c 0x58ceff0001f9f000

def z1058 : W := mkw 0x10024041ffef5981 0xe840090107ffbd66 0x50000001ffffffff 0x0140000007ffffff

def z1059 : W := mkw 0x0a8240016cac0001 0x802a090005b2b000 0xffffc001fffc001f 0x7fffff0007fff000

def z1060 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0xafffefde00000000 0x7ebfffbf78000000

def z1061 : W := mkw 0x2efd9dbe0000003e 0x00bbf676f8000000 0xafffddfe00000000 0x7ebfff77f8000000

def z1062 : W := mkw 0x10024041ffef5801 0xe040090107ffbd60 0x50000001fffc181f 0x0140000007fff060

def z1063 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fffc001fffc000e 0x5dffff0007fff000

def z1064 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c3981ffe73f 0xff31c0f0e607ff9c

def z1065 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00700015 0xfebffffff801c000

def z1066 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x33bfc0007e7c0008 0x50ceff0001f9f000

def z1067 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0xccb1d3e78e7d9cff 0xff32c74f9e39f673

def z1068 : W := mkw 0x0fe92b0081400000 0x003fa4ac02050000 0xefffffc181f3e037 0xffbfffff0607cf80

def z1069 : W := mkw 0x10024041ffffdc41 0xf440090107ffff71 0x50000001fffffcff 0x0140000007fffff3

def z1070 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3c60e7d98ed 0xda02c74f1839f663

def z1071 : W := mkw 0x0b892b0000000000 0x002e24ac00000000 0xaf8fffc000000000 0xdebe3fff00000000

def z1072 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81f00717 0xffbffffffe07c01c

def z1073 : W := mkw 0x0b842b4d5a035989 0x282e10ad35680d66 0xffce3ffffe03ffef 0xffff38fffff80fff

def z1074 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe01800710 0xfebffffff806001c

def z1075 : W := mkw 0x2fedab8e8140000e 0x00bfb6ae3a050000 0xefffc3c781f00017 0x7fbfff0f1e07c000

def z1076 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xdf703c39f1f3e73f 0xbf7dc0f0e7c7cf9c

def z1077 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81f26712 0xffbffffffe07c99c

def z1078 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xa3ffd3fe00000000 0xfa8fff4ff8000000

def z1079 : W := mkw 0x10024041efed0801 0xe040090107bfb420 0x50000001fffd983f 0x0140000007fff660

def z1080 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc001fff0000f 0x1fffff0007ffc000

def z1081 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c703c3981f3e726 0x8d31c0f0e607cf9c

def z1082 : W := mkw 0x0006000c20880188 0x0800180030822006 0xb34e023e718c1ffb 0xf6cd3808f9c6307f

def z1083 : W := mkw 0x2ffdbfbf5802503f 0x00bff6fefd600940 0xfffffffffe02600f 0xfffffffffff80980

def z1084 : W := mkw 0x000000415a035801 0x2000000105680d60 0xdc803fc1fe03f82f 0x9f7200ff07f80fe0

def z1085 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0x2fffddc000000000 0x0cbfff7700000000

def z1086 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3e60e7d98cc 0xfa02c74f9839f663

def z1087 : W := mkw 0x0010d4f20635ae74 0xb4004353c818d6b9 0x80b1d3fe0e7d9ffd 0xfa02c74ff839f67f

def z1088 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffe019fffe031f 0x7fffff8067fff80c

def z1089 : W := mkw 0x0b842b4d5a035809 0x202e10ad35680d60 0xff8e3fc7fe03f82f 0xdffe38ff1ff80fe0

def z1090 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e223e718c1fd8 0xf6cd3888f9c6307f

def z1091 : W := mkw 0x10024001edec0001 0xc040090007b7b000 0xf3ffc001fffc001f 0x7fcfff0007fff000

def z1092 : W := mkw 0x0002404026bd8c40 0xb4000901009af631 0x100000007ffd9cff 0x0040000001fff673

def z1093 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa3cfe3fe01820733 0xf68f3f8ff806081c

def z1094 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00001829 0xfebffffff8000060

def z1095 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe018e1ffb 0xfebffffff806387f

def z1096 : W := mkw 0x0b842b4d5a035989 0x282e10ad35680d66 0xdf803ffffe0fffff 0xff7e00fffff83fff

def z1097 : W := mkw 0x2a8d898e0000000e 0x00aa362638000000 0x208fc1c600000000 0x40823f0718000000

def z1098 : W := mkw 0x2ffdbfbf4800003f 0x00bff6fefd200000 0xefffffff8e000004 0xffbffffffe380000

def z1099 : W := mkw 0x2ffdbfbe8140003e 0x00bff6fefa050000 0xefffffff81f3e037 0xffbffffffe07cf80

def z1100 : W := mkw 0x0b802b415a035981 0x282e00ad05680d66 0xdf803fc1fe03ffef 0x9f7e00ff07f80fff

def z1101 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x23fffffe00000000 0xf08ffffff8000000

def z1102 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00020023 0xfebffffff8000800

def z1103 : W := mkw 0x0a8009414a014801 0x202a002505280520 0xdf803dc1fe03e02f 0x9f7e00f707f80f80

def z1104 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xaffffffe00021820 0xfebffffff8000860

def z1105 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xbffffffe71821f3b 0xfefffffff9c6087c

def z1106 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xefffffff8073e437 0xffbffffffe01cf90

def z1107 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfb1ffc1fe03f82f 0xff7ec7ff07f80fe0

def z1108 : W := mkw 0x210dab8e0000000e 0x008436ae38000000 0x200fc3c600000000 0x40803f0f18000000

def z1109 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc1fe0ff83f 0xff7e00ff07f83fe0

def z1110 : W := mkw 0x2ffdbfbfd942723f 0x00bff6feff6509c8 0xfffffffff1826302 0xffffffffffc6098c

def z1111 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803dc1fe03e00f 0x1f7e00f707f80f80

def z1112 : W := mkw 0x247d94be8150a63e 0x1091f652fa054298 0xecffffff81f3e737 0xffb3fffffe07cf9c

def z1113 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c303c3981f3e737 0x8930c0f0e607cf9c

def z1114 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffc201fffc183f 0xffffff0807fff060

def z1115 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0xafcfeffe00000000 0xf6bf3fbff8000000

def z1116 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe01820302 0xfebffffff806080c

def z1117 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffdc01fffde01f 0x7fffff7007fff780

def z1118 : W := mkw 0x047094b28150a634 0x1011c252ca054298 0xccf1ffff81ffffff 0xff33c7fffe07ffff

def z1119 : W := mkw 0x1eeb4901edec4001 0xc07bad2407b7b100 0xffffcc01fffc601f 0x7fffff3007fff180

def z1120 : W := mkw 0x046004108150a610 0x1011801042054298 0xcc403c1981f3e737 0x8f3100f06607cf9c

def z1121 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803fc1ff83ff3f 0x9f7e00ff07fe0ffc

def z1122 : W := mkw 0x2ffdbfbe100211be 0x08bff6fef8400846 0xaffffffe01821ff3 0xfebffffff806087f

def z1123 : W := mkw 0x0ff9bba200000024 0x003fe6ee88000000 0xafffffe600000000 0xfebfffff98000000

def z1124 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb3ffe23e718e1ffb 0xfecfff88f9c6387f

def z1125 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xafcffffe00000000 0xfebf3ffff8000000

def z1126 : W := mkw 0x0b802b414a014801 0x202e00ad05280520 0xdf803fc1fe01e00f 0x9f7e00ff07f80780

def z1127 : W := mkw 0x0a8009414a014801 0x202a002505280520 0x5f801dc1fe01e00c 0x197e007707f80780

def z1128 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff8071e435 0xffbffffffe01c790

def z1129 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3e60fff9fff 0xfa02c74f983ffe7f

def z1130 : W := mkw 0x2ffdbfbf5802103f 0x00bff6fefd600840 0xfffffffffe02182f 0xfffffffffff80860

def z1131 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f803fc1fe03f82a 0x957e00ff07f80fe0

def z1132 : W := mkw 0x0010d4f20635ae74 0xb4004353c818d6b9 0x80f1fffe0fffffff 0xfe03c7fff83fffff

def z1133 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1f3fe0e7f9ffd 0xfa02c7cff839fe7f

def z1134 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81ffffff 0xffbffffffe07ffff

def z1135 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703c1981f3e317 0x2f31c0f06607cf8c

def z1136 : W := mkw 0x0114b2ae0010842c 0x100452cab8004210 0xa3fff3fe01f38737 0xfe8fffcff807ce1c

def z1137 : W := mkw 0x2ffdbfbe100211be 0x08bff6fef8400846 0xaffffffe000e1ff9 0xfebffffff800387f

def z1138 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdfc03ff9fe03f82f 0xbf7f00ffe7f80fe0

def z1139 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1ffe60e7ffcfd 0xfa02c7ff9839fff3

def z1140 : W := mkw 0x10024041fffffe01 0xf040090107fffff8 0x50000001ffffff3f 0x0140000007fffffc

def z1141 : W := mkw 0x0010d0e20635ae64 0xb40043438818d6b9 0x80b1d3e60e7ffffd 0xfa02c74f9839ffff

def z1142 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe000c04d0 0xfebffffff8003013

def z1143 : W := mkw 0x0100224012031800 0x2004008900480c60 0xdf803fc1fe03f82f 0x9f7e00ff07f80fe0

def z1144 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c703c3981f3e732 0xa531c0f0e607cf9c

def z1145 : W := mkw 0x0fed2b0c00000008 0x003fb4ac30000000 0xaffffffe00000000 0xfebffffff8000000

def z1146 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x8cb1ffe60e7d9cfd 0xfe32c7ff9839f673

def z1147 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa38fd3c600000000 0xda8e3f4f18000000

def z1148 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff81f1e714 0xffbffffffe07c79c

def z1149 : W := mkw 0x000000008150a600 0x1000000002054298 0xcc403c3981f3e737 0xaf3100f0e607cf9c

def z1150 : W := mkw 0x2ffdbfbf5802503f 0x00bff6fefd600940 0xfffffffff003e027 0xffffffffffc00f80

def z1151 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e023e718c1ff9 0xf2cd3808f9c6307f

def z1152 : W := mkw 0x047094b28150a634 0x1011c252ca054298 0xccf1fdf981f3e737 0xaf33c7f7e607cf9c

def z1153 : W := mkw 0x10024041efed0841 0xe440090107bfb421 0x50000001fffc18df 0x0140000007fff063

def z1154 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7f7fc001fffc001f 0x65fdff0007fff000

def z1155 : W := mkw 0x2ffdbfbf4800403f 0x00bff6fefd200100 0xefffffff80006000 0xffbffffffe000180

def z1156 : W := mkw 0x2ffdbfbe0010a63e 0x10bff6fef8004298 0xaffffffe00000700 0xfebffffff800001c

def z1157 : W := mkw 0x047914308150a630 0x1011e450c2054298 0xec7ffc3981f3e737 0xefb1fff0e607cf9c

def z1158 : W := mkw 0x0000404006250800 0xa000010100189420 0x80b1d3e60e7d9cfd 0xfa02c74f9839f673

def z1159 : W := mkw 0x0b842b4d5a035989 0x282e10ad35680d66 0xdfc03fffff83ffff 0xbf7f00fffffe0fff

def z1160 : W := mkw 0x047014308150a630 0x1011c050c2054298 0x4c702c3981f3e737 0x2531c0b0e607cf9c

def z1161 : W := mkw 0x2fedaf9e0000001e 0x00bfb6be78000000 0x23cfc3de00000000 0x508f3f0f78000000

def z1162 : W := mkw 0x257dbfbe0000003e 0x0095f6fef8000000 0xa0fffffe00000000 0xfa83fffff8000000

def z1163 : W := mkw 0x0b842b4d5a035989 0x282e10ad35680d66 0xdf803fc7fe03f8ef 0x9f7e00ff1ff80fe3

def z1164 : W := mkw 0x1eeb4411edec2211 0xc07bad1047b7b088 0xffffc019fffc031f 0x7fffff0067fff00c

def z1165 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0xccb1dfe78e7dfcfd 0xfb32c77f9e39f7f3

def z1166 : W := mkw 0x247994b28150a636 0x1091e652ca054298 0xcc71fc3981f3e737 0xaf31c7f0e607cf9c

def z1167 : W := mkw 0x0002404036af19c0 0xac00090100dabc67 0x100000007e0c18c8 0x0040000001f83063

def z1168 : W := mkw 0x2a89898200000006 0x00aa262608000000 0x238fc1c000000000 0x508e3f0700000000

def z1169 : W := mkw 0x0a8009414a014801 0x202a002505280520 0x5f801dc1fe01e006 0x0d7e007707f80780

def z1170 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703e3f81f3fff7 0xaf31c0f8fe07cfff

def z1171 : W := mkw 0x047094b28150a674 0x1411c252ca054299 0xcc703c3f81f3e7f7 0xaf31c0f0fe07cf9f

def z1172 : W := mkw 0x000240417ebfddc1 0xbc00090105faff77 0x50000001ffffffff 0x0140000007ffffff

def z1173 : W := mkw 0x0a8009415a035801 0x202a002505680d60 0x5c801dc1fe03e006 0x0972007707f80f80

def z1174 : W := mkw 0x3fef2f1df9ca119b 0x48ffbcbc77e72846 0x7f4e2c19f1820302 0x05fd38b067c6080c

def z1175 : W := mkw 0x047014308150a630 0x1011c050c2054298 0xcc703e3f81f3e737 0xff31c0f8fe07cf9c

def z1176 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xaffffffe00020720 0xfebffffff800081c

def z1177 : W := mkw 0x2ffdbfbe0010843e 0x10bff6fef8004210 0xaffffffe01f38737 0xfebffffff807ce1c

def z1178 : W := mkw 0x0ff93f308150a630 0x103fe4fcc2054298 0xeffffff981f3e737 0xffbfffffe607cf9c

def z1179 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0x238fffc600000000 0xd08e3fff18000000

def z1180 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xbffffffe700e1cfb 0xfefffffff9c03873

def z1181 : W := mkw 0x0ef990a200000024 0x003be64288000000 0xafffd1c000000000 0x7ebfff4700000000

def z1182 : W := mkw 0x0460000081400000 0x0011800002050000 0xcc703c3981f3e737 0xaf31c0f0e607cf9c

def z1183 : W := mkw 0x2ef99db28150a636 0x10bbe676ca054298 0xefffddc181f1e017 0x7fbfff770607c780

def z1184 : W := mkw 0x2ffdbfbe9152b63e 0x10bff6fefa454ad8 0xfffffffff1f3ff3f 0xffffffffffc7cffc

def z1185 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff8073e027 0xffbffffffe01cf80

def z1186 : W := mkw 0x2b8dab8e1002118e 0x08ae36ae38400846 0x238fe3fe00021fe0 0xd08e3f8ff800087f

def z1187 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xefffffff8183e722 0xffbffffffe060f9c

def z1188 : W := mkw 0x2ffdbfbf5802503f 0x00bff6fefd600940 0xfffffffff002782b 0xffffffffffc009e0

def z1189 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fbfc001fffc001f 0x59feff0007fff000

def z1190 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa3bfc3c600000000 0x7a8eff0f18000000

def z1191 : W := mkw 0x3eeb4d11edec0013 0xc0fbad3447b7b000 0xffffcc01fffc001f 0x7fffff3007fff000

def z1192 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xbffffffe70001808 0xfefffffff9c00060

def z1193 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xbffffffe7000000b 0xfefffffff9c00000

def z1194 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xafffffd800000000 0x9ebfffff60000000

def z1195 : W := mkw 0x1ef9d4f3cf75ae75 0xf47be753cf3dd6b9 0x4cb1ddc18e71e004 0x0932c7770639c780

def z1196 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xaffffffe01f18735 0xfebffffff807c61c

def z1197 : W := mkw 0x0002404036bf9dc0 0xbc00090100dafe77 0x100000007e7d9cfd 0x0040000001f9f673

def z1198 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0x7fbfc001fe700004 0x09feff0007f9c000

def z1199 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3c60e7d9cfd 0x5802c74f1839f673

def z1200 : W := mkw 0x2ffdbfbe9152b7be 0x18bff6fefa454ade 0xefffffff81f3fff7 0xffbffffffe07cfff

def z1201 : W := mkw 0x04725470b7ffbff0 0xbc11c951c2dffeff 0xdc703c39ffffffff 0xaf71c0f0e7ffffff

def z1202 : W := mkw 0x2ffdbfbe8150a63e 0x10bff6fefa054298 0xaffffffe01f3e730 0xfebffffff807cf9c

def z1203 : W := mkw 0x2ffdbfbe1002103e 0x00bff6fef8400840 0xbffffffe70020002 0xfefffffff9c00800

def z1204 : W := mkw 0x10024041effd8c41 0xf440090107bff631 0x50000001fffd801f 0x0140000007fff600

def z1205 : W := mkw 0x2b9dbfbe0000003e 0x00ae76fef8000000 0xa3cffffe00000000 0xf68f3ffff8000000

def z1206 : W := mkw 0x0114b6fe1213bffc 0x3c0452dbf8484eff 0x00003ffe0003ffe0 0x800000fff8000fff

def z1207 : W := mkw 0x10024041ffff9dc1 0xfc40090107fffe77 0x50000001ffff9fff 0x0140000007fffe7f

def z1208 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f801dc1fe01e004 0x097e007707f80780

def z1209 : W := mkw 0x01062b0c308a5188 0x080418ac30c22946 0xb34e2e3e718e7ffb 0xf6cd38b8f9c639ff

def z1210 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0xafbfffc600000000 0xdebeffff18000000

def z1211 : W := mkw 0x2ffdbfbe8140003e 0x00bff6fefa050000 0xefffffff81f20737 0xffbffffffe07c81c

def z1212 : W := mkw 0x1a8b40016cac0001 0xc06a2d0005b2b000 0xb3ffc0007ffc001f 0x7ecfff0001fff000

def z1213 : W := mkw 0x0106220c308a1188 0x0804188830c22846 0xb34e323e718f9fff 0xfecd38c8f9c63e7f

def z1214 : W := mkw 0x0002404036af19c0 0xac00090100dabc67 0x100000007f8e1ffb 0x0040000001fe387f

def z1215 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0xdf803ff9fe03ff2f 0x9f7e00ffe7f80ffc

def z1216 : W := mkw 0x2ffdbfbf4800003f 0x00bff6fefd200000 0xfffffffffe03e02f 0xfffffffffff80f80

def z1217 : W := mkw 0x2ee9898200000006 0x00bba62608000000 0xafffc1c000000000 0x7ebfff0700000000

def z1218 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xb3ffc0007ffc001b 0x76cfff0001fff000

def z1219 : W := mkw 0x1eeb4001edec0001 0xc07bad0007b7b000 0xffffec01fffe601f 0x7fffffb007fff980

def z1220 : W := mkw 0x1b826b01edec0001 0xc06e09ac07b7b000 0xdf803fc1fffc001f 0x9f7e00ff07fff000

def z1221 : W := mkw 0x0460041081402210 0x0011801042050088 0xcc703c1981f3e337 0xaf31c0f06607cf8c

def z1222 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x80b1d3e60e7c1cd8 0xfa02c74f9839f073

def z1223 : W := mkw 0x2b8dab8e0000000e 0x00ae36ae38000000 0xa38fc3e6000c1cf9 0xf28e3f0f98003073

def z1224 : W := mkw 0x2efd9dbe8150a63e 0x10bbf676fa054298 0x6cffddff81f1e714 0x69b3ff77fe07c79c

def z1225 : W := mkw 0x2ffdbfbe0000003e 0x00bff6fef8000000 0x2fffffde00000000 0x5cbfffff78000000

def z1226 : W := mkw 0x0010d0e206358c64 0xb40043438818d631 0x00b1d3e60e7d9cec 0xd802c74f9839f673

def z1227 : W := mkw 0x2fedab8e0000000e 0x00bfb6ae38000000 0xafffffc600000000 0xfebfffff18000000

def z1228 : W := mkw 0x0b802b415a035801 0x202e00ad05680d60 0x5f803dc1fe03f82f 0x0d7e00f707f80fe0

def z1229 : W := mkw 0x2b9dbbae0000002e 0x00ae76eeb8000000 0x23bfd3c600000000 0x588eff4f18000000

def z1230 : W := mkw 0x10024041effdae41 0xf440090107bff6b9 0x50000001ffffffff 0x0140000007ffffff

def z1231 : W := mkw 0x1a8b4001edec0001 0xc06a2d0007b7b000 0xf3bfc001fffc001f 0x7bceff0007fff000

def z1232 : W := mkw 0x2ffdbfbe8140223e 0x00bff6fefa050088 0xefffffff81f26317 0xffbffffffe07c98c

def z1233 : W := mkw 0x2ef99db200000036 0x00bbe676c8000000 0x2fbfddc000000000 0x58beff7700000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z9])],[(0,[z0,z1,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z3,z4,z11,z6]),(0,[z12,z0,z1,z2,z3,z13,z6]),(1,[z0,z1,z2,z3,z4,z14]),(0,[z15,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z17,z4,z6]),(0,[z0,z1,z2,z18,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z19]),(0,[z20,z0,z1,z2,z3,z4,z6]),(0,[z0,z21,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z3,z4,z23,z23])],[(0,[z0,z1,z2,z3,z4,z24,z6]),(0,[z25,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z26,z27,z4,z6]),(0,[z0,z1,z28,z2,z3,z4,z6])],[(0,[z29,z0,z30,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z4,z6]),(1,[z32,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z34,z6]),(0,[z0,z1,z35,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z37,z6,z38]),(0,[z0,z39,z40,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z3,z4,z42]),(0,[z0,z1,z2,z3,z43,z4,z23]),(0,[z44,z0,z1,z2,z3,z45,z4]),(0,[z46,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z19,z6]),(0,[z47,z0,z1,z2,z48,z4,z6]),(0,[z49,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z9,z6,z23])],[(0,[z50,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z4,z6]),(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z54,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z55]),(0,[z0,z1,z56,z2,z3,z4,z6])]],
   [[(0,[z20,z1,z2,z3,z13,z4,z6]),(0,[z0,z1,z57,z2,z3,z4,z6]),(0,[z58,z0,z21,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z59])],[(0,[z0,z1,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z61,z4,z6]),(0,[z62,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z63,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z4,z23]),(0,[z0,z1,z2,z3,z65,z4,z6]),(0,[z0,z1,z2,z3,z4,z66,z23]),(1,[z0,z1,z2,z3,z4,z67])],[(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z70,z4,z6]),(1,[z0,z1,z2,z71,z4,z72]),(0,[z0,z1,z2,z3,z73,z4,z6])],[(0,[z0,z1,z74,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z6]),(0,[z0,z1,z2,z48,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z76,z6]),(0,[z77,z78,z1,z2,z3,z4,z6])],[(1,[z0,z1,z79,z3,z4,z6]),(0,[z20,z0,z1,z51,z3,z4,z6]),(1,[z58,z1,z2,z3,z80,z6]),(0,[z0,z1,z2,z27,z4,z6,z72]),(0,[z0,z1,z2,z3,z4,z6,z81]),(0,[z82,z0,z1,z2,z3,z4,z6]),(0,[z0,z21,z1,z2,z3,z4,z83]),(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z86]),(0,[z0,z1,z2,z3,z4,z86,z6])],[(0,[z87,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z88,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z3,z4,z6]),(0,[z0,z1,z2,z3,z90,z4,z6])],[(0,[z58,z1,z2,z51,z3,z4,z6]),(1,[z0,z91,z2,z3,z4,z92]),(0,[z77,z0,z1,z2,z3,z4,z23]),(1,[z93,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z94,z4,z34,z6])],[(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z97,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z98,z3,z4,z6]),(0,[z0,z1,z40,z2,z3,z4,z23]),(0,[z0,z99,z1,z2,z3,z4,z100]),(0,[z0,z1,z2,z3,z101,z4,z6])],[(0,[z0,z102,z1,z2,z3,z4,z6]),(0,[z103,z0,z1,z2,z3,z4,z9]),(1,[z0,z1,z2,z65,z4,z6])],[(0,[z47,z0,z2,z104,z3,z4,z6]),(0,[z105,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z48,z106,z4,z6]),(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z108,z6]),(0,[z0,z109,z1,z2,z110,z4,z6])],[(1,[z0,z1,z111,z3,z4,z6]),(0,[z103,z0,z1,z2,z112,z4,z6]),(0,[z0,z39,z1,z2,z3,z4,z6]),(1,[z44,z0,z1,z2,z4,z113])],[(0,[z114,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z115,z2,z3,z4,z23]),(0,[z15,z0,z2,z3,z4,z16,z6]),(0,[z77,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z116,z6]),(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z118,z2,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z45,z4]),(0,[z0,z1,z2,z120,z3,z4,z6]),(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z122,z4,z6]),(0,[z0,z1,z2,z3,z4,z123,z6]),(0,[z77,z0,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z124])],[(1,[z0,z1,z2,z3,z125,z6]),(0,[z0,z1,z30,z2,z3,z4,z9]),(0,[z126,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z80,z9]),(0,[z127,z0,z1,z2,z3,z4,z6]),(0,[z128,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z129,z3,z4,z6]),(0,[z0,z1,z2,z3,z130,z4,z6])]],
   [[(0,[z0,z1,z115,z2,z3,z131,z6]),(0,[z132,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z133]),(0,[z0,z1,z2,z134,z3,z4,z6]),(1,[z0,z135,z2,z3,z4,z6]),(0,[z0,z1,z135,z2,z3,z4,z6]),(0,[z136,z0,z1,z2,z3,z4,z6])],[(0,[z41,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z137,z2,z3,z66,z6])],[(0,[z0,z1,z2,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z138]),(0,[z139,z0,z1,z2,z3,z4,z6]),(0,[z140,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z3,z4,z6])],[(0,[z0,z1,z2,z3,z142,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z37]),(0,[z0,z1,z2,z3,z143,z4,z6]),(1,[z78,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z144,z3,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z145,z0,z1,z2,z3,z4,z9]),(0,[z0,z109,z1,z2,z3,z110,z6])],[(0,[z146,z0,z147,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z106,z4,z6])],[(0,[z29,z0,z1,z2,z3,z4,z19]),(0,[z145,z0,z1,z2,z3,z4,z72]),(0,[z0,z1,z2,z3,z148,z4,z6]),(1,[z0,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z149,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z150,z6]),(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z151,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z152,z0,z1,z2,z3,z4,z6]),(0,[z153,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z40,z51,z3,z4,z6]),(0,[z0,z154,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z155,z6]),(0,[z0,z1,z2,z94,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z156,z6]),(0,[z0,z1,z2,z3,z157,z4,z6]),(1,[z145,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z4,z16,z9]),(0,[z0,z21,z1,z2,z158,z4,z6]),(0,[z0,z1,z159,z2,z3,z4,z9]),(1,[z0,z1,z3,z4,z9,z23]),(0,[z0,z160,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z161,z4,z6])],[(1,[z0,z1,z2,z3,z131,z6]),(0,[z162,z0,z1,z2,z3,z4,z6]),(1,[z41,z0,z2,z3,z4,z42])],[(0,[z20,z50,z1,z2,z3,z4,z6]),(0,[z58,z20,z1,z2,z3,z4,z6]),(0,[z163,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z48,z4,z6,z72]),(0,[z0,z1,z164,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z165,z4,z6])],[(0,[z0,z1,z2,z3,z4,z166,z6])],[(0,[z0,z1,z2,z3,z4,z167,z6]),(0,[z0,z1,z2,z3,z4,z168,z6]),(0,[z0,z1,z137,z2,z3,z4,z155]),(0,[z0,z1,z2,z2,z3,z4,z23])],[(0,[z0,z1,z2,z169,z3,z4,z6]),(0,[z0,z1,z2,z3,z170,z4,z6]),(0,[z85,z93,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z6])],[(0,[z0,z1,z2,z71,z3,z4,z23]),(0,[z0,z1,z2,z3,z171,z4,z6])]],
   [[(0,[z29,z0,z1,z79,z3,z4,z6]),(0,[z172,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z51,z3,z4,z23]),(0,[z0,z1,z2,z48,z173,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z23]),(0,[z0,z1,z2,z3,z174,z4,z6]),(0,[z0,z1,z2,z175,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z176,z6]),(0,[z0,z1,z28,z2,z3,z4,z108]),(0,[z0,z1,z2,z3,z4,z177,z6]),(0,[z0,z1,z2,z3,z4,z178,z9]),(0,[z0,z179,z1,z2,z3,z4,z6]),(0,[z0,z180,z1,z2,z3,z4,z6])],[(0,[z0,z99,z2,z3,z27,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z23]),(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z72,z124])],[(0,[z0,z1,z2,z3,z183,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z9]),(0,[z0,z1,z2,z3,z184,z4,z6]),(0,[z185,z0,z39,z2,z3,z4,z6]),(0,[z0,z99,z1,z2,z3,z4,z9]),(0,[z0,z91,z2,z3,z4,z6,z92]),(0,[z0,z1,z2,z3,z186,z4,z6]),(0,[z187,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z188,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z189,z6])],[(0,[z0,z1,z2,z3,z4,z190,z6]),(0,[z191,z0,z1,z2,z3,z4,z6]),(0,[z0,z192,z1,z2,z3,z4,z6]),(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z194,z3,z4,z6]),(0,[z195,z0,z1,z2,z3,z4,z6])],[(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z50,z0,z1,z115,z3,z4,z6]),(1,[z20,z1,z115,z3,z4,z6]),(0,[z197,z85,z1,z2,z3,z4,z6]),(0,[z0,z198,z1,z2,z3,z4,z6]),(1,[z0,z109,z1,z2,z110,z6])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z45,z4,z124])],[(0,[z29,z0,z1,z111,z3,z4,z6]),(0,[z0,z1,z2,z51,z3,z4,z23]),(0,[z1,z2,z3,z13,z4,z80,z6]),(0,[z0,z1,z2,z3,z4,z42,z38]),(0,[z200,z0,z1,z2,z3,z4,z6]),(0,[z0,z201,z1,z2,z3,z4,z6])]],
   [[(0,[z146,z0,z1,z2,z3,z4,z9]),(0,[z202,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z203,z4,z6]),(0,[z0,z204,z1,z2,z3,z4,z6]),(0,[z12,z0,z21,z1,z2,z3,z6]),(1,[z0,z1,z2,z205,z4,z6]),(0,[z0,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z207,z4,z6]),(0,[z0,z1,z2,z3,z4,z208,z6]),(0,[z0,z1,z2,z3,z181,z4,z6])],[(0,[z209,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z28,z2,z3,z4,z9])],[(0,[z29,z0,z1,z2,z3,z125,z6]),(0,[z0,z1,z2,z210,z3,z4,z6]),(0,[z20,z0,z1,z115,z3,z4,z6]),(0,[z0,z99,z1,z2,z27,z4,z6]),(0,[z0,z21,z2,z3,z64,z4,z6]),(0,[z0,z1,z2,z3,z4,z34,z9])],[(0,[z211,z0,z1,z2,z173,z4,z6]),(0,[z0,z1,z2,z3,z13,z16,z6]),(0,[z212,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z213,z4,z6]),(0,[z0,z1,z2,z3,z4,z214,z6]),(0,[z0,z1,z2,z3,z4,z23,z38]),(0,[z0,z1,z2,z215,z3,z4,z6]),(0,[z216,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z217,z23])],[(0,[z0,z1,z2,z3,z218,z4,z6]),(0,[z0,z1,z2,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z219,z4,z6]),(0,[z220,z0,z1,z2,z3,z4,z6]),(0,[z0,z91,z1,z2,z221,z4,z6]),(0,[z0,z1,z2,z3,z222,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z223]),(0,[z0,z1,z2,z3,z224,z4,z6])],[(0,[z0,z1,z225,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z226,z4,z6])],[(0,[z0,z1,z2,z227,z3,z4,z6]),(0,[z0,z228,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z229]),(0,[z0,z1,z2,z3,z4,z6,z230]),(0,[z0,z1,z2,z3,z70,z4,z9])],[(0,[z231,z0,z1,z2,z3,z4,z6]),(0,[z20,z146,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z232,z6]),(0,[z0,z1,z233,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z234])],[(0,[z29,z0,z1,z2,z3,z4,z23]),(0,[z119,z0,z91,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z217,z6])],[(0,[z0,z1,z2,z3,z235,z4,z6]),(0,[z236,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z137,z3,z66,z6]),(0,[z0,z1,z137,z2,z3,z4,z23]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z124]),(0,[z0,z1,z2,z3,z4,z238,z6])],[(0,[z239,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z173,z3,z4,z23]),(1,[z185,z0,z104,z3,z4,z6]),(0,[z240,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z241])],[(0,[z0,z1,z2,z3,z4,z6,z83]),(0,[z0,z1,z2,z3,z4,z242,z9])],[(0,[z243,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z6,z244]),(0,[z0,z1,z2,z245,z3,z4,z6]),(0,[z185,z0,z1,z2,z143,z4,z6]),(0,[z0,z246,z1,z2,z3,z4,z6]),(0,[z0,z1,z137,z2,z3,z181,z6]),(0,[z0,z1,z2,z3,z247,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z248]),(0,[z0,z1,z2,z71,z4,z6,z72])]],
   [[(0,[z146,z1,z2,z51,z3,z4,z6]),(0,[z50,z0,z1,z2,z3,z4,z6]),(0,[z0,z249,z1,z2,z3,z4,z6]),(0,[z185,z0,z1,z2,z3,z4,z6]),(0,[z0,z39,z2,z3,z27,z4,z6]),(0,[z0,z1,z2,z3,z250,z4,z6])],[(0,[z0,z251,z1,z2,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z37]),(0,[z145,z1,z2,z3,z4,z37,z6]),(0,[z185,z0,z1,z2,z3,z252,z6]),(0,[z0,z39,z1,z2,z3,z4,z9]),(0,[z0,z21,z1,z2,z3,z4,z23]),(0,[z77,z0,z1,z2,z3,z253,z6]),(0,[z0,z1,z137,z2,z3,z4,z6]),(0,[z254,z0,z1,z2,z3,z4,z9])],[(0,[z0,z1,z2,z3,z255,z4,z6]),(0,[z0,z1,z2,z3,z4,z256,z6]),(0,[z257,z0,z1,z2,z3,z4,z6]),(0,[z258,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z259,z3,z4,z23])],[(0,[z0,z1,z2,z260,z3,z4,z6]),(0,[z261,z0,z1,z2,z3,z4,z6]),(0,[z0,z262,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z263,z6]),(0,[z0,z264,z1,z2,z3,z4,z6])],[(0,[z119,z1,z2,z3,z4,z6,z38]),(0,[z0,z1,z2,z3,z4,z37,z23]),(0,[z0,z265,z1,z2,z3,z4,z6]),(0,[z0,z1,z266,z2,z3,z4,z6])],[(0,[z267,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z268]),(0,[z0,z1,z2,z3,z4,z269,z6]),(0,[z0,z1,z2,z3,z270,z4,z6]),(0,[z271,z0,z1,z2,z3,z4,z23])],[(0,[z272,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z112,z4,z23]),(0,[z47,z0,z99,z2,z3,z4,z6]),(0,[z0,z91,z1,z2,z3,z4,z42]),(0,[z0,z1,z2,z3,z4,z42,z6]),(0,[z0,z273,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z274,z23])],[(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z0,z1,z2,z3,z4,z276,z6]),(0,[z1,z2,z173,z3,z112,z4,z6]),(1,[z0,z1,z2,z3,z4,z277]),(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z279,z6])]],
   [[],[(0,[z0,z1,z2,z3,z4,z6,z280])],[(0,[z185,z281,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z45,z4,z42])],[(0,[z271,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z282,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z4,z23]),(0,[z0,z1,z2,z3,z106,z4,z9]),(1,[z0,z1,z2,z3,z4,z155]),(0,[z0,z1,z2,z3,z283,z4,z6])],[(0,[z0,z1,z2,z3,z4,z284,z6]),(0,[z0,z1,z2,z3,z4,z285,z6]),(0,[z185,z0,z1,z2,z205,z4,z6]),(0,[z286,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z287,z4,z6]),(0,[z0,z1,z2,z3,z4,z288,z6]),(0,[z0,z1,z2,z3,z4,z274,z6])],[(0,[z0,z1,z2,z3,z4,z289,z6]),(0,[z0,z1,z290,z2,z3,z4,z6]),(0,[z291,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z292]),(0,[z0,z1,z2,z293,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z294,z6]),(0,[z0,z91,z1,z2,z65,z4,z6]),(0,[z41,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z295,z4,z42])],[(1,[z0,z1,z115,z3,z4,z23]),(0,[z0,z1,z2,z296,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z23]),(0,[z145,z0,z91,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z297,z4,z6]),(0,[z0,z1,z2,z3,z4,z298,z6]),(0,[z0,z1,z299,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z6])],[(1,[z50,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z300]),(0,[z0,z1,z2,z104,z3,z4,z9])]],
   [[(1,[z0,z1,z2,z3,z4,z24]),(0,[z0,z1,z2,z3,z301,z4,z6]),(0,[z0,z1,z28,z2,z3,z4,z59]),(0,[z0,z302,z1,z2,z3,z4,z6]),(0,[z0,z1,z303,z2,z3,z4,z6])],[(0,[z304,z0,z1,z2,z3,z4,z6]),(0,[z0,z305,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z306,z6])],[(0,[z0,z1,z2,z3,z307,z4,z6]),(0,[z47,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z66,z6]),(0,[z0,z1,z2,z3,z308,z4,z6])],[(1,[z304,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z309,z3,z4,z6]),(0,[z0,z1,z2,z3,z310,z4,z6]),(0,[z41,z0,z1,z2,z3,z4,z92]),(0,[z311,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z168,z9])],[(0,[z0,z1,z312,z2,z3,z4,z6]),(0,[z313,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z48,z3,z4,z6])],[(0,[z0,z147,z1,z2,z3,z4,z23]),(0,[z0,z314,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z315,z4,z6]),(0,[z0,z1,z316,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z124])],[(0,[z0,z1,z2,z317,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z318]),(0,[z0,z1,z2,z3,z319,z4,z6]),(0,[z320,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z137,z2,z3,z4,z234]),(0,[z0,z1,z2,z321,z3,z4,z9])],[(0,[z0,z1,z115,z2,z3,z322,z6]),(1,[z0,z1,z2,z3,z4,z323]),(0,[z0,z1,z2,z3,z4,z9,z42]),(0,[z85,z0,z1,z2,z3,z66,z6])]],
   [[(0,[z0,z324,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z325,z4,z6])],[(1,[z0,z1,z2,z3,z4,z326]),(0,[z211,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z40,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z327,z6]),(0,[z0,z1,z2,z3,z328,z4,z6])],[(0,[z329,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z330,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z38]),(0,[z0,z91,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z33,z6])],[(0,[z0,z147,z1,z2,z3,z4,z6]),(0,[z331,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z13,z6]),(0,[z0,z1,z2,z3,z332,z4,z6]),(0,[z0,z1,z2,z3,z333,z4,z6]),(0,[z0,z1,z2,z71,z3,z4,z113])],[(0,[z50,z0,z1,z2,z3,z4,z138]),(0,[z0,z1,z2,z3,z110,z66,z6]),(0,[z0,z1,z2,z3,z4,z9,z334]),(0,[z335,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z336,z6]),(0,[z0,z1,z2,z337,z3,z4,z6]),(1,[z0,z1,z2,z315,z4,z6]),(0,[z0,z1,z2,z338,z3,z4,z6])],[(0,[z0,z339,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z45,z4,z23])],[(0,[z0,z1,z115,z2,z3,z4,z176]),(0,[z211,z0,z1,z2,z3,z4,z6]),(0,[z340,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z77,z0,z1,z2,z3,z4,z342])]],
   [[(0,[z0,z1,z2,z343,z3,z4,z6]),(0,[z0,z91,z1,z2,z3,z4,z6]),(0,[z0,z1,z344,z2,z3,z4,z6])],[(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z115,z3,z4,z6,z23]),(0,[z0,z1,z2,z3,z4,z6,z346]),(0,[z0,z1,z347,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z348,z4,z6]),(0,[z349,z0,z1,z2,z3,z4,z23]),(0,[z0,z109,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z295,z4,z23]),(0,[z0,z1,z2,z3,z350,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z351])],[(0,[z352,z0,z1,z2,z3,z4,z6])],[(0,[z353,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z28,z26,z3,z4,z6])],[(0,[z0,z1,z2,z3,z354,z4,z6]),(0,[z0,z1,z2,z355,z3,z4,z6]),(0,[z0,z1,z2,z356,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z45,z4,z6])],[(0,[z103,z211,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z173,z3,z4,z277]),(0,[z58,z0,z1,z2,z3,z66,z6]),(0,[z0,z1,z2,z3,z4,z357,z6]),(0,[z358,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z359,z2,z3,z4,z6]),(1,[z85,z0,z1,z3,z181,z6])],[(0,[z146,z147,z1,z2,z3,z4,z6]),(0,[z0,z1,z360,z2,z3,z4,z6]),(1,[z0,z1,z2,z143,z4,z6]),(0,[z0,z1,z2,z3,z181,z16,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z361,z3,z4,z6]),(0,[z0,z1,z362,z2,z3,z4,z6]),(0,[z349,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z363,z6]),(0,[z0,z109,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z364,z6])]],
   [[(1,[z29,z30,z2,z3,z4,z6]),(0,[z20,z1,z115,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z80]),(1,[z0,z1,z2,z3,z252,z6]),(0,[z0,z99,z1,z2,z48,z4,z6]),(0,[z0,z1,z2,z3,z366,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z367]),(0,[z0,z1,z137,z3,z4,z66,z6])],[(0,[z0,z1,z2,z368,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z176]),(0,[z0,z369,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z370,z6])],[(0,[z0,z1,z2,z3,z4,z6,z371]),(0,[z0,z1,z2,z372,z3,z4,z6]),(1,[z0,z1,z2,z3,z373,z4]),(0,[z0,z1,z2,z3,z295,z45,z6])],[(0,[z0,z1,z2,z3,z374,z4,z6]),(0,[z0,z1,z2,z375,z3,z4,z9])],[(0,[z0,z1,z2,z3,z4,z125,z6]),(0,[z50,z0,z1,z2,z3,z4,z24]),(0,[z0,z1,z2,z3,z376,z4,z6]),(0,[z12,z0,z1,z2,z3,z4,z23]),(0,[z145,z0,z1,z2,z3,z45,z4])],[(0,[z377,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z27,z112,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z378]),(0,[z0,z1,z2,z3,z4,z379,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z50,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z4,z6,z380]),(0,[z185,z0,z1,z2,z3,z4,z9]),(0,[z381,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z382,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z64,z6]),(0,[z0,z1,z26,z3,z106,z4,z6]),(0,[z383,z0,z1,z2,z3,z4,z6])],[(0,[z0,z40,z2,z104,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z342]),(0,[z384,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z385,z6]),(0,[z0,z1,z2,z3,z386,z4,z6]),(0,[z0,z1,z2,z387,z3,z4,z6])]],
   [[(0,[z0,z1,z388,z2,z3,z4,z6]),(1,[z0,z1,z74,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z389]),(0,[z0,z1,z2,z71,z3,z4,z6]),(0,[z0,z1,z2,z3,z390,z4,z6])],[(0,[z0,z391,z1,z2,z3,z4,z6]),(1,[z281,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z42]),(1,[z0,z1,z2,z3,z4,z59]),(1,[z0,z1,z28,z26,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z110,z4,z34,z6]),(1,[z0,z1,z2,z3,z161,z4]),(0,[z0,z1,z2,z3,z392,z4,z6]),(0,[z0,z1,z2,z3,z393,z4,z6])],[(0,[z0,z1,z388,z30,z2,z3,z6]),(0,[z0,z1,z2,z394,z3,z4,z6]),(0,[z395,z0,z1,z2,z3,z4,z6]),(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z113]),(0,[z0,z1,z2,z397,z3,z4,z6])],[(0,[z20,z0,z1,z2,z3,z4,z9]),(0,[z398,z0,z1,z2,z3,z4,z6])],[(0,[z29,z1,z30,z2,z3,z4,z6]),(0,[z399,z0,z1,z2,z3,z4,z6]),(0,[z0,z400,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z295,z4,z124])],[(0,[z29,z0,z1,z2,z3,z4,z326]),(0,[z0,z1,z2,z3,z401,z4,z6]),(0,[z0,z402,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z403,z23])],[(0,[z404,z0,z1,z2,z3,z4,z6]),(0,[z0,z405,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z406,z6]),(0,[z0,z1,z2,z3,z4,z42,z72]),(0,[z0,z1,z2,z3,z4,z248,z6]),(1,[z0,z1,z2,z3,z4,z223]),(0,[z0,z1,z2,z3,z4,z6,z407])],[(0,[z29,z146,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z408,z4,z6]),(0,[z0,z1,z2,z3,z409,z4,z23])]],
   [[(1,[z0,z1,z410,z2,z3,z4]),(0,[z1,z2,z51,z3,z112,z4,z6]),(0,[z12,z1,z2,z3,z13,z4,z6]),(0,[z411,z0,z1,z2,z3,z4,z6]),(0,[z412,z0,z1,z2,z3,z4,z6]),(0,[z413,z0,z1,z2,z3,z4,z6])],[(0,[z414,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z415,z4,z6]),(0,[z0,z416,z1,z2,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z23]),(0,[z271,z0,z1,z2,z3,z4,z9])],[(0,[z417,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z4,z418,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z100]),(0,[z0,z1,z3,z181,z4,z66,z6]),(0,[z0,z1,z2,z3,z4,z420,z23])],[(0,[z103,z1,z2,z3,z112,z4,z6]),(0,[z0,z1,z2,z3,z4,z421,z6]),(0,[z422,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z423,z6]),(0,[z0,z1,z2,z3,z4,z23,z72]),(0,[z0,z1,z2,z3,z424,z4,z6])],[(0,[z0,z1,z2,z3,z425,z4,z6]),(0,[z0,z1,z2,z3,z426,z4,z6]),(0,[z0,z1,z2,z3,z427,z4,z6]),(0,[z0,z1,z2,z428,z3,z4,z6]),(0,[z429,z0,z1,z2,z3,z4,z6])],[(0,[z216,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z80,z6]),(0,[z85,z0,z1,z2,z3,z181,z6])],[(0,[z50,z1,z2,z51,z3,z4,z6]),(0,[z430,z0,z1,z2,z3,z4,z6]),(0,[z58,z1,z2,z3,z4,z80,z6]),(0,[z0,z431,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z432,z6]),(0,[z433,z0,z1,z2,z3,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z110,z4,z23])],[(1,[z0,z1,z2,z213,z4,z6]),(0,[z0,z1,z2,z435,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z92]),(0,[z0,z1,z2,z3,z253,z4,z6]),(0,[z0,z1,z2,z3,z436,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z373,z4,z6]),(0,[z0,z1,z2,z3,z4,z437,z6])]],
   [[(0,[z0,z1,z438,z2,z3,z4,z6]),(0,[z439,z0,z1,z2,z3,z4,z6]),(0,[z440,z0,z1,z2,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z38]),(0,[z0,z21,z1,z2,z315,z4,z6]),(0,[z0,z1,z2,z3,z64,z4,z9]),(0,[z0,z1,z2,z441,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z66,z9])],[(0,[z442,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z443]),(0,[z0,z1,z2,z3,z4,z444,z6])],[(0,[z0,z445,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z446,z4,z6]),(0,[z0,z1,z2,z447,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z113]),(0,[z0,z1,z2,z3,z4,z448,z6]),(0,[z0,z1,z40,z2,z3,z4,z449]),(0,[z0,z1,z2,z48,z3,z4,z9]),(0,[z15,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z110,z181,z6])],[(0,[z29,z0,z1,z2,z3,z4,z6]),(0,[z146,z0,z30,z2,z3,z4,z6]),(0,[z0,z1,z410,z30,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z138]),(0,[z0,z39,z1,z104,z3,z4,z6]),(0,[z0,z1,z450,z2,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z6,z23]),(0,[z0,z1,z2,z48,z112,z4,z6]),(0,[z0,z451,z1,z2,z3,z4,z6]),(0,[z85,z0,z1,z3,z181,z4,z6]),(0,[z0,z452,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z173,z3,z4,z6]),(0,[z0,z1,z2,z453,z3,z4,z6]),(0,[z0,z21,z1,z2,z3,z64,z6]),(0,[z77,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z26,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z113,z23]),(0,[z0,z1,z2,z3,z4,z9,z454]),(0,[z0,z455,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z124])],[(0,[z47,z0,z39,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z22,z6]),(0,[z0,z1,z2,z3,z456,z4,z6])],[(0,[z58,z0,z1,z2,z3,z4,z23]),(1,[z0,z1,z457,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z458,z6]),(0,[z0,z1,z40,z2,z3,z4,z9]),(0,[z44,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z459,z0,z1,z2,z3,z4,z6]),(0,[z47,z0,z2,z48,z3,z4,z6]),(0,[z460,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z461,z3,z4,z6]),(0,[z0,z1,z462,z2,z3,z4,z6]),(1,[z103,z1,z2,z112,z4,z6]),(0,[z0,z1,z2,z3,z66,z16,z6]),(0,[z0,z1,z2,z3,z4,z463,z6]),(0,[z0,z1,z2,z3,z464,z4,z6]),(0,[z0,z1,z465,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z161,z4,z34])],[(1,[z466,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z467,z6]),(0,[z0,z1,z2,z3,z468,z4,z6]),(0,[z0,z1,z2,z3,z469,z4,z6]),(1,[z0,z99,z2,z27,z4,z6]),(0,[z0,z21,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z470,z3,z4,z6]),(0,[z335,z0,z1,z2,z3,z4,z9])],[(0,[z0,z1,z115,z2,z3,z4,z9]),(0,[z58,z0,z1,z2,z3,z181,z6]),(1,[z15,z0,z2,z3,z16,z6]),(0,[z0,z1,z2,z259,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z6])],[(0,[z0,z1,z2,z3,z4,z471,z6]),(0,[z0,z1,z2,z3,z4,z23,z244])],[(0,[z58,z0,z1,z2,z3,z4,z6]),(0,[z12,z0,z1,z2,z3,z66,z6]),(0,[z0,z1,z2,z3,z4,z37,z6]),(1,[z0,z1,z2,z3,z4,z108])],[(0,[z0,z1,z2,z3,z183,z4,z80]),(0,[z0,z1,z2,z457,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z472,z6])],[(0,[z0,z473,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z112,z4,z6]),(0,[z0,z1,z2,z3,z80,z16,z6])]],
   [[(0,[z0,z1,z474,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z449]),(0,[z0,z1,z2,z3,z4,z475,z6])],[(0,[z0,z1,z2,z94,z48,z4,z6])],[(0,[z0,z476,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z477,z6]),(0,[z0,z1,z2,z3,z4,z478,z6]),(0,[z41,z0,z91,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z479,z4,z6])],[(0,[z480,z0,z1,z2,z3,z4,z6]),(0,[z41,z119,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z481])],[(0,[z0,z1,z2,z482,z3,z4,z6]),(0,[z145,z0,z1,z2,z3,z4,z38]),(0,[z281,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z4,z6]),(0,[z0,z91,z1,z2,z3,z4,z92]),(0,[z0,z1,z2,z3,z4,z72,z92]),(1,[z0,z1,z2,z3,z253,z6]),(0,[z0,z1,z483,z2,z3,z4,z6]),(1,[z197,z1,z2,z3,z4,z6])],[(0,[z145,z119,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z484,z4,z6]),(0,[z0,z1,z2,z3,z4,z485,z6]),(0,[z0,z1,z2,z486,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z9])],[(0,[z304,z0,z1,z30,z2,z3,z6]),(0,[z0,z487,z1,z2,z3,z4,z6])],[(0,[z119,z0,z1,z2,z3,z4,z6]),(0,[z488,z0,z1,z2,z3,z4,z6]),(0,[z0,z369,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z94,z3,z4,z9])]],
   [[(0,[z0,z1,z2,z489,z3,z4,z6]),(0,[z145,z0,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z45,z4,z92])],[(0,[z0,z1,z79,z2,z3,z4,z6]),(0,[z8,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z490,z2,z3,z4,z6])],[(0,[z20,z1,z2,z3,z112,z4,z6]),(0,[z103,z0,z1,z2,z3,z4,z23]),(0,[z0,z39,z1,z40,z3,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z475])],[(0,[z29,z0,z1,z2,z213,z4,z6]),(0,[z0,z491,z1,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z492,z4,z6]),(0,[z0,z1,z493,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z494,z4,z6])],[(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z158,z3,z4,z6]),(0,[z496,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z497,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z9])],[(0,[z498,z0,z1,z2,z3,z4,z6]),(0,[z0,z499,z1,z2,z3,z4,z6]),(0,[z77,z0,z500,z2,z3,z4,z6]),(0,[z501,z0,z1,z2,z3,z4,z6]),(0,[z0,z502,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z503,z6]),(0,[z0,z1,z2,z94,z27,z4,z6]),(0,[z0,z1,z28,z2,z26,z4,z6]),(0,[z0,z93,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z504,z23]),(0,[z0,z1,z2,z71,z3,z4,z9]),(0,[z0,z505,z1,z2,z3,z4,z6])],[(0,[z0,z1,z30,z2,z3,z4,z23]),(0,[z0,z506,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z80,z23]),(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z9]),(0,[z0,z1,z2,z4,z113,z6,z72])]],
   [[(0,[z119,z0,z1,z74,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z38,z92]),(0,[z0,z1,z2,z3,z4,z6,z67]),(0,[z396,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z71,z3,z4,z72])],[(0,[z0,z1,z508,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z9]),(0,[z0,z1,z2,z3,z4,z9,z72])],[(0,[z466,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z509,z4,z6])],[(0,[z0,z1,z510,z2,z3,z4,z6]),(0,[z0,z1,z2,z511,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z512,z6])],[(0,[z0,z1,z2,z3,z513,z4,z6]),(1,[z0,z1,z2,z3,z322,z6]),(0,[z0,z1,z2,z3,z4,z6,z38]),(0,[z514,z0,z1,z2,z3,z4,z6]),(0,[z515,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z504,z6])],[(0,[z466,z0,z1,z30,z2,z3,z4]),(0,[z145,z0,z1,z2,z3,z4,z23]),(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z27,z110,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z92])],[(0,[z517,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z51,z3,z4,z9]),(0,[z0,z1,z518,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z519,z6]),(0,[z0,z1,z2,z520,z3,z4,z6]),(0,[z0,z1,z2,z3,z521,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z522]),(0,[z0,z1,z2,z3,z4,z523,z6])],[(0,[z0,z1,z2,z3,z4,z6,z524])]],
   [[(0,[z0,z1,z525,z2,z3,z4,z6]),(0,[z526,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z133]),(0,[z0,z1,z2,z3,z45,z403,z6])],[(0,[z0,z1,z2,z3,z4,z403,z113])],[(0,[z0,z1,z2,z527,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z16,z23]),(0,[z0,z1,z159,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z295,z4,z6])],[(0,[z0,z1,z2,z3,z4,z528,z6]),(0,[z145,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z529,z4,z6]),(0,[z0,z1,z530,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z531,z4,z6]),(0,[z0,z1,z532,z2,z3,z4,z6]),(0,[z0,z533,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z432,z9]),(1,[z0,z1,z2,z3,z45,z403])],[(0,[z0,z1,z2,z3,z4,z6,z326]),(0,[z0,z534,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z42,z6,z92]),(1,[z0,z500,z2,z3,z4,z6]),(0,[z0,z1,z2,z535,z3,z4,z6]),(0,[z8,z0,z1,z159,z3,z4,z6])],[(0,[z536,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z537,z3,z4,z6]),(0,[z0,z538,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z539,z6]),(0,[z0,z1,z2,z3,z540,z4,z6])],[(0,[z0,z1,z2,z3,z4,z541,z6]),(0,[z0,z1,z2,z3,z4,z542,z6]),(0,[z543,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z145,z41,z0,z1,z2,z3,z4]),(0,[z185,z0,z1,z104,z3,z4,z6]),(0,[z0,z1,z2,z3,z544,z4,z6]),(0,[z0,z1,z2,z3,z4,z16,z6]),(0,[z0,z1,z2,z94,z3,z34,z6]),(0,[z0,z1,z545,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z546,z6])],[(0,[z29,z0,z1,z2,z3,z4,z9]),(1,[z0,z1,z2,z3,z4,z86])],[(0,[z0,z1,z2,z3,z4,z6,z547]),(0,[z0,z1,z137,z2,z3,z4,z9]),(0,[z0,z548,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z173,z3,z4,z9]),(0,[z12,z0,z1,z2,z3,z181,z6]),(0,[z0,z1,z2,z3,z549,z4,z6])],[(0,[z0,z1,z2,z3,z13,z4,z23]),(0,[z0,z1,z550,z2,z3,z4,z6]),(0,[z0,z99,z1,z2,z3,z4,z23])],[(0,[z0,z551,z1,z2,z3,z4,z6]),(0,[z0,z1,z115,z2,z3,z4,z318]),(0,[z12,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z552,z6]),(0,[z0,z1,z2,z3,z4,z6,z23]),(0,[z44,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z295,z6,z124])],[(0,[z0,z1,z553,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z554,z6]),(0,[z0,z1,z555,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z322,z6]),(0,[z103,z0,z1,z2,z173,z4,z6]),(0,[z119,z0,z1,z457,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z371]),(0,[z44,z0,z1,z2,z3,z4,z72]),(0,[z0,z1,z2,z3,z556,z4,z6])]],
   [[(1,[z0,z1,z2,z3,z255,z6]),(0,[z0,z1,z2,z3,z4,z557,z6]),(0,[z0,z1,z2,z3,z4,z6,z558]),(0,[z0,z1,z2,z3,z559,z4,z6]),(0,[z0,z1,z2,z173,z3,z4,z323]),(0,[z0,z1,z2,z3,z4,z560,z6]),(0,[z0,z1,z2,z3,z4,z561,z6]),(0,[z0,z21,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z71,z3,z295,z4])],[(1,[z146,z147,z2,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z562,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z563,z6]),(0,[z0,z1,z2,z3,z4,z6,z564])],[(0,[z0,z1,z2,z565,z3,z4,z6]),(0,[z566,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z6]),(0,[z0,z1,z2,z3,z4,z567,z6]),(0,[z0,z1,z2,z3,z568,z4,z6]),(0,[z0,z1,z28,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z181,z34,z6]),(0,[z187,z0,z1,z2,z3,z4,z6]),(0,[z569,z0,z1,z2,z3,z4,z6]),(0,[z570,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z4,z34,z23]),(1,[z0,z1,z2,z3,z295,z124])],[(0,[z0,z1,z2,z3,z4,z571,z6]),(0,[z572,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z48,z110,z4,z6])],[(0,[z0,z1,z2,z3,z131,z4,z6]),(0,[z0,z1,z2,z3,z112,z4,z9]),(1,[z211,z1,z2,z173,z4,z6]),(0,[z0,z1,z573,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z574,z4,z6]),(0,[z0,z400,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z575,z4,z6])],[(0,[z0,z1,z2,z3,z4,z252,z6]),(0,[z0,z2,z3,z64,z4,z16,z6]),(0,[z576,z0,z1,z2,z3,z4,z6]),(0,[z85,z0,z1,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z403,z6])],[(0,[z146,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z318]),(0,[z8,z0,z1,z115,z3,z4,z6]),(0,[z0,z1,z2,z3,z577,z4,z6]),(0,[z0,z1,z2,z3,z578,z4,z6]),(0,[z0,z579,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z92]),(0,[z0,z1,z2,z3,z4,z580,z6]),(0,[z581,z0,z1,z2,z3,z4,z23])]],
   [[(0,[z0,z1,z582,z2,z3,z4,z6]),(0,[z0,z21,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z409,z4,z6])],[(0,[z583,z0,z1,z2,z3,z4,z6]),(0,[z584,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z37,z92]),(0,[z0,z2,z48,z3,z27,z4,z6]),(0,[z0,z585,z1,z2,z3,z4,z6]),(0,[z77,z0,z1,z2,z3,z4,z367]),(0,[z0,z1,z28,z2,z106,z4,z6]),(0,[z0,z1,z586,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z587,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6]),(0,[z0,z1,z2,z3,z27,z4,z9]),(0,[z0,z500,z1,z2,z3,z4,z6]),(0,[z588,z0,z1,z2,z3,z4,z6]),(0,[z589,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z410,z2,z3,z4,z6]),(0,[z0,z590,z1,z2,z3,z4,z6]),(0,[z77,z0,z1,z3,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z420,z6])],[(0,[z591,z0,z1,z2,z3,z4,z6]),(0,[z592,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z593,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z4,z594,z6]),(1,[z314,z1,z2,z3,z4,z6]),(0,[z77,z0,z135,z2,z3,z4,z6]),(0,[z581,z0,z1,z2,z3,z4,z6])],[(0,[z0,z595,z1,z2,z3,z4,z6]),(0,[z15,z0,z1,z2,z3,z64,z6]),(0,[z77,z0,z1,z28,z3,z4,z6])],[(0,[z20,z211,z1,z2,z3,z4,z6]),(0,[z596,z0,z1,z2,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z72]),(0,[z185,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z597]),(0,[z0,z1,z2,z3,z110,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z598,z6]),(0,[z599,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z230]),(0,[z0,z1,z2,z3,z403,z6,z124])],[(0,[z47,z0,z1,z2,z3,z4,z9]),(0,[z600,z0,z1,z2,z3,z4,z6]),(1,[z8,z0,z1,z3,z4,z9]),(0,[z0,z601,z1,z2,z3,z4,z6])],[(1,[z0,z1,z388,z2,z3,z6]),(0,[z0,z1,z2,z3,z602,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z58,z12,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z604,z3,z4,z6]),(0,[z0,z39,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z6,z223]),(0,[z605,z0,z1,z2,z3,z4,z6])],[(0,[z15,z0,z1,z2,z3,z4,z6])],[(0,[z0,z147,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z4,z242,z6]),(0,[z606,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z115,z104,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z607,z6])],[(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z609,z0,z1,z2,z3,z4,z6]),(0,[z185,z0,z1,z2,z3,z4,z280]),(0,[z0,z1,z2,z3,z4,z6,z100]),(0,[z0,z1,z2,z3,z610,z4,z6]),(0,[z0,z1,z2,z26,z3,z4,z6]),(0,[z0,z1,z2,z3,z611,z4,z6]),(0,[z0,z1,z612,z2,z3,z4,z6])],[(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z614,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z454]),(0,[z44,z0,z1,z2,z3,z295,z4])]],
   [[(0,[z0,z1,z2,z615,z3,z4,z6]),(0,[z254,z0,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z2,z3,z4,z9]),(0,[z47,z0,z1,z2,z27,z4,z6]),(0,[z0,z1,z616,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z234])],[(0,[z0,z1,z2,z3,z4,z617,z6]),(0,[z0,z1,z2,z3,z4,z292,z6]),(0,[z0,z91,z1,z2,z3,z4,z9]),(1,[z0,z1,z2,z3,z4,z367])],[(0,[z618,z0,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z2,z112,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z619,z3,z4,z6]),(0,[z620,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z90,z6]),(0,[z0,z1,z2,z3,z4,z6,z621])],[(0,[z29,z0,z1,z2,z3,z255,z6]),(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z15,z12,z0,z1,z2,z3,z6]),(0,[z185,z0,z1,z2,z3,z4,z232]),(0,[z15,z0,z21,z2,z3,z4,z6]),(0,[z0,z1,z2,z623,z3,z4,z6]),(0,[z0,z1,z2,z3,z106,z4,z23])],[(0,[z624,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z625,z6]),(0,[z8,z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z45,z4,z9]),(0,[z0,z109,z1,z2,z94,z4,z6])],[(0,[z0,z626,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z627,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z628]),(0,[z0,z1,z2,z629,z3,z4,z6]),(0,[z0,z32,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z342,z6]),(1,[z77,z0,z1,z106,z4,z6]),(0,[z0,z1,z630,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z104,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z6,z631]),(0,[z0,z109,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z295,z4,z9])],[(0,[z632,z0,z1,z2,z3,z4,z6]),(0,[z58,z0,z1,z2,z3,z13,z6]),(0,[z145,z0,z1,z2,z3,z4,z113]),(1,[z0,z39,z40,z3,z4,z6]),(0,[z0,z633,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z634,z4,z6]),(1,[z0,z1,z2,z94,z34,z6]),(0,[z0,z1,z2,z3,z635,z4,z6])],[(1,[z0,z1,z2,z60,z4,z6]),(0,[z0,z1,z636,z2,z3,z4,z6]),(0,[z0,z1,z637,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z638,z4,z6]),(0,[z0,z1,z2,z3,z4,z334,z6])],[(0,[z0,z1,z2,z221,z3,z4,z6]),(0,[z0,z1,z2,z94,z3,z110,z6]),(1,[z0,z1,z2,z3,z4,z475])],[(0,[z0,z1,z2,z3,z4,z6,z639]),(0,[z640,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z641])],[(0,[z642,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z643,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z34,z6])],[(1,[z0,z1,z2,z3,z365,z4]),(0,[z0,z1,z2,z104,z3,z4,z6]),(0,[z0,z1,z2,z644,z3,z4,z6]),(0,[z0,z1,z2,z3,z295,z4,z92])],[(0,[z119,z0,z1,z2,z3,z295,z4]),(1,[z0,z1,z2,z3,z4,z22])]],
   [[(0,[z211,z1,z2,z51,z3,z4,z6]),(0,[z0,z1,z645,z2,z3,z4,z6]),(0,[z12,z0,z1,z2,z3,z80,z6]),(0,[z0,z1,z2,z3,z646,z4,z6]),(0,[z647,z0,z1,z2,z3,z4,z6]),(0,[z648,z0,z1,z2,z3,z4,z6])],[(0,[z29,z0,z147,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z183,z4]),(0,[z185,z314,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z649,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z650,z6]),(0,[z0,z1,z2,z3,z4,z651,z6]),(0,[z652,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z653])],[],[(0,[z103,z0,z1,z2,z3,z4,z6]),(0,[z12,z0,z1,z2,z3,z4,z9]),(0,[z0,z99,z1,z2,z3,z4,z292]),(0,[z0,z1,z2,z3,z654,z4,z6])],[(0,[z0,z1,z115,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z449])],[(0,[z147,z1,z30,z2,z3,z4,z6]),(0,[z1,z115,z2,z51,z3,z4,z6]),(0,[z0,z1,z655,z2,z3,z4,z6]),(0,[z0,z1,z2,z321,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z656]),(0,[z1,z2,z51,z3,z13,z4,z6])],[(0,[z657,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z66,z6]),(0,[z78,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z373,z4,z34])]],
   [[(0,[z0,z1,z30,z2,z3,z4,z6]),(0,[z0,z1,z2,z658,z3,z4,z6]),(0,[z0,z1,z659,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z80,z6]),(0,[z0,z1,z2,z3,z660,z4,z6]),(0,[z661,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z662,z4,z6])],[(1,[z0,z1,z2,z3,z4,z83]),(0,[z0,z1,z663,z2,z3,z4,z6]),(0,[z0,z1,z2,z664,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z0,z1,z2,z3,z45,z4,z403])],[(0,[z1,z30,z2,z51,z3,z4,z6]),(0,[z0,z2,z104,z3,z27,z4,z6]),(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z667,z4,z6])],[(0,[z0,z1,z668,z2,z3,z4,z6]),(0,[z669,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z6,z72])],[(0,[z0,z1,z2,z3,z4,z670,z6]),(0,[z0,z1,z2,z671,z3,z4,z6]),(0,[z0,z1,z2,z672,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z403,z9]),(0,[z0,z1,z2,z3,z295,z4,z403])],[(0,[z211,z1,z2,z173,z3,z4,z6]),(0,[z58,z15,z0,z1,z2,z3,z6]),(0,[z0,z1,z673,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z323]),(0,[z674,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z71,z3,z45,z4]),(0,[z0,z1,z2,z3,z4,z403,z72])],[(0,[z0,z1,z675,z2,z3,z4,z6]),(0,[z185,z0,z1,z2,z3,z90,z6]),(0,[z0,z1,z2,z48,z26,z4,z6]),(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z92])]],
   [[(0,[z0,z1,z51,z104,z3,z4,z6]),(1,[z12,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z4,z42,z37]),(0,[z85,z0,z1,z2,z3,z4,z9])],[(0,[z0,z1,z677,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z678]),(0,[z0,z1,z2,z3,z679,z4,z6]),(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z0,z109,z1,z2,z3,z34,z6])],[(0,[z44,z0,z1,z2,z48,z4,z6]),(0,[z77,z0,z1,z2,z26,z4,z6])],[(0,[z20,z1,z30,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z680,z4,z6]),(0,[z145,z0,z1,z2,z3,z295,z4]),(0,[z0,z1,z40,z2,z3,z4,z14]),(0,[z0,z1,z2,z3,z4,z14,z6]),(0,[z0,z1,z159,z2,z3,z4,z6])],[(0,[z0,z1,z2,z681,z3,z4,z6]),(0,[z77,z32,z1,z2,z3,z4,z6]),(0,[z77,z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z682,z4,z6]),(1,[z0,z1,z2,z3,z4,z280]),(0,[z0,z1,z2,z3,z683,z4,z6]),(0,[z0,z1,z2,z3,z110,z4,z9])],[(0,[z29,z0,z1,z2,z60,z4,z6]),(0,[z0,z1,z2,z3,z4,z684,z6]),(0,[z0,z1,z685,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z686,z4,z6]),(0,[z44,z0,z1,z2,z4,z113,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z50,z0,z1,z2,z3,z4,z23]),(1,[z119,z1,z2,z3,z4,z38]),(0,[z185,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z687,z3,z4,z6]),(0,[z0,z1,z159,z3,z4,z6,z23])]],
   [[(0,[z0,z688,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z689,z3,z4,z6]),(0,[z690,z0,z1,z2,z3,z4,z6]),(0,[z15,z0,z1,z2,z3,z4,z9]),(1,[z0,z1,z2,z221,z4,z6]),(1,[z0,z1,z159,z3,z4,z23])],[(0,[z185,z0,z2,z104,z3,z4,z6]),(0,[z0,z1,z2,z375,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z597,z6]),(0,[z44,z0,z1,z2,z71,z4,z6])],[(0,[z0,z1,z2,z3,z4,z178,z6]),(0,[z58,z0,z1,z2,z3,z80,z6]),(1,[z0,z1,z2,z3,z4,z232]),(0,[z0,z1,z2,z27,z106,z4,z6]),(0,[z0,z1,z2,z691,z3,z4,z6])],[(0,[z20,z0,z1,z2,z3,z4,z23]),(0,[z692,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z693,z6]),(0,[z0,z1,z2,z26,z3,z4,z9]),(0,[z197,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z9]),(0,[z0,z1,z2,z3,z4,z6,z694])],[(0,[z0,z695,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z696]),(0,[z0,z1,z2,z3,z697,z4,z6]),(0,[z0,z1,z2,z173,z27,z4,z6]),(0,[z0,z99,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z42,z23]),(0,[z0,z1,z2,z3,z4,z6,z698]),(0,[z699,z0,z1,z2,z3,z4,z6])],[(0,[z58,z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z205,z3,z4,z6]),(1,[z0,z1,z2,z158,z4,z6]),(0,[z0,z1,z2,z3,z4,z700,z6]),(0,[z41,z0,z2,z3,z4,z42,z6])],[(0,[z701,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z277,z6]),(0,[z0,z1,z702,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z27,z4,z6]),(0,[z0,z1,z703,z2,z3,z4,z6]),(0,[z0,z1,z2,z704,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z705,z6]),(0,[z0,z1,z2,z3,z4,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z131,z23]),(0,[z0,z1,z2,z3,z4,z707]),(0,[z0,z1,z2,z94,z34,z6])],[(0,[z1,z510,z51,z3,z4,z6]),(0,[z0,z1,z2,z143,z4,z23]),(0,[z0,z500,z2,z3,z253,z6]),(0,[z0,z1,z2,z3,z4,z708]),(0,[z0,z201,z1,z2,z110,z6])],[(0,[z29,z30,z2,z60,z4,z6]),(0,[z0,z500,z2,z3,z4,z9])],[(0,[z145,z1,z2,z3,z479,z4]),(0,[z0,z1,z137,z3,z66,z155]),(0,[z0,z1,z194,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z709]),(0,[z281,z1,z2,z3,z90,z6]),(0,[z0,z2,z104,z143,z4,z6]),(0,[z710,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z711,z4,z6])],[(0,[z0,z1,z712,z3,z4,z6]),(0,[z0,z1,z2,z3,z713,z6]),(0,[z145,z1,z2,z3,z4,z37]),(0,[z320,z0,z1,z3,z4,z9]),(0,[z197,z1,z2,z3,z4,z86]),(0,[z0,z1,z3,z4,z9,z23])],[(0,[z0,z1,z2,z3,z131,z6]),(0,[z0,z714,z2,z3,z4,z6]),(0,[z0,z1,z2,z205,z90,z6]),(0,[z0,z1,z3,z715,z4,z6]),(0,[z0,z1,z2,z672,z4,z72]),(0,[z0,z1,z2,z716,z4,z6]),(0,[z0,z1,z2,z315,z4,z83]),(0,[z41,z0,z2,z3,z4,z42]),(0,[z77,z0,z1,z106,z4,z342]),(0,[z0,z1,z2,z3,z43,z124]),(0,[z0,z717,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z718])],[(0,[z0,z719,z2,z3,z4,z6]),(0,[z358,z1,z115,z3,z4,z6]),(0,[z0,z1,z3,z207,z4,z23]),(0,[z0,z1,z2,z720,z4,z6])]],
   [[(0,[z0,z721,z2,z3,z4,z6]),(0,[z581,z1,z51,z3,z4,z23]),(0,[z0,z1,z2,z3,z722,z4]),(0,[z0,z1,z2,z3,z183,z4]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z452,z2,z3,z4,z92]),(0,[z0,z1,z2,z3,z724,z4])],[(0,[z119,z1,z673,z2,z3,z4]),(0,[z0,z1,z2,z3,z725,z6]),(0,[z0,z1,z2,z3,z4,z726]),(0,[z0,z1,z2,z3,z727,z23]),(0,[z0,z1,z2,z3,z4,z728])],[(0,[z0,z1,z2,z729,z4,z6]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z1,z2,z731,z4,z6]),(0,[z0,z1,z2,z732,z3,z4]),(0,[z0,z1,z2,z3,z733,z6]),(0,[z0,z1,z2,z3,z4,z734]),(0,[z0,z1,z3,z4,z706,z9])],[(0,[z0,z1,z2,z3,z4,z735]),(0,[z20,z1,z115,z3,z4,z23]),(0,[z199,z1,z2,z3,z13,z6]),(0,[z0,z736,z2,z3,z4,z6]),(0,[z0,z109,z1,z2,z110,z23])],[(0,[z0,z1,z51,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z1,z2,z3,z738,z4]),(0,[z0,z533,z2,z27,z4,z6])],[(0,[z0,z1,z2,z3,z255,z9]),(0,[z605,z0,z1,z3,z4,z23])],[(0,[z146,z147,z2,z3,z4,z9]),(0,[z581,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z739,z6]),(0,[z0,z1,z2,z205,z4,z23]),(0,[z740,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z741,z16,z6]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z0,z1,z2,z3,z743,z4]),(0,[z0,z1,z2,z3,z409,z504])],[(0,[z0,z1,z2,z3,z744,z4]),(0,[z0,z1,z2,z94,z34,z223])]],
   [[(0,[z0,z1,z2,z158,z4,z9]),(0,[z77,z78,z1,z106,z4,z6])],[(0,[z0,z1,z745,z2,z3,z6]),(0,[z20,z1,z115,z3,z4,z6]),(0,[z0,z1,z2,z746,z4,z6]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z44,z0,z1,z2,z4,z561]),(0,[z605,z0,z1,z3,z181,z6]),(0,[z0,z109,z1,z2,z110,z6])],[(0,[z0,z1,z2,z3,z4,z749]),(0,[z211,z1,z2,z173,z4,z9]),(0,[z0,z1,z2,z3,z45,z580]),(0,[z0,z1,z2,z750,z34,z6])],[(0,[z0,z751,z1,z2,z3,z4]),(0,[z690,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z752]),(0,[z0,z1,z2,z753,z4,z6])],[(0,[z0,z1,z2,z3,z4,z754]),(0,[z211,z1,z2,z755,z4,z6]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z703,z3,z66,z6])],[(0,[z0,z1,z2,z759,z4,z6]),(0,[z349,z0,z2,z3,z4,z420]),(1,[z0,z1,z2,z4,z760])],[(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z0,z1,z245,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z763]),(0,[z0,z1,z2,z764,z3,z4]),(0,[z0,z1,z447,z3,z4,z23]),(0,[z399,z1,z2,z3,z4,z38]),(0,[z0,z1,z3,z4,z448,z23])],[(0,[z0,z1,z2,z765,z4,z6]),(0,[z12,z1,z2,z3,z13,z6]),(0,[z0,z1,z553,z3,z181,z6]),(0,[z0,z1,z2,z3,z295,z698])]],
   [[(0,[z0,z1,z766,z3,z4,z6]),(0,[z0,z767,z2,z3,z4,z6]),(0,[z0,z768,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z113,z760])],[(0,[z29,z388,z30,z2,z3,z6]),(0,[z0,z1,z769,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z770]),(0,[z0,z1,z137,z3,z66,z23]),(0,[z0,z1,z2,z3,z771,z4])],[(0,[z0,z1,z2,z3,z772,z4]),(0,[z1,z51,z3,z13,z4,z23]),(0,[z419,z0,z2,z3,z4,z42]),(0,[z314,z1,z2,z3,z4,z9]),(0,[z185,z0,z104,z3,z4,z23]),(0,[z0,z1,z260,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z773])],[(0,[z20,z1,z774,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z775]),(0,[z1,z2,z3,z4,z776,z6]),(0,[z0,z1,z2,z4,z6,z777]),(0,[z0,z1,z2,z259,z4,z230]),(0,[z0,z1,z2,z3,z295,z437]),(0,[z0,z1,z2,z71,z4,z760])],[(0,[z0,z1,z778,z3,z4,z6]),(0,[z0,z1,z2,z3,z252,z280]),(0,[z0,z1,z2,z3,z4,z779]),(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z137,z3,z781,z6]),(0,[z85,z93,z1,z3,z181,z6]),(0,[z335,z0,z2,z3,z4,z432])],[(0,[z0,z1,z782,z3,z4,z6]),(0,[z58,z1,z2,z3,z80,z9]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z3,z4,z279,z23])],[(0,[z0,z1,z388,z2,z3,z9]),(0,[z0,z451,z2,z27,z4,z6]),(0,[z0,z1,z137,z3,z66,z6])]],
   [[(0,[z1,z2,z173,z755,z4,z6]),(0,[z119,z1,z2,z3,z4,z334]),(0,[z0,z1,z2,z221,z4,z6]),(0,[z0,z534,z1,z2,z110,z6]),(0,[z0,z1,z159,z3,z4,z23])],[(0,[z0,z1,z2,z785,z4,z6]),(0,[z0,z1,z2,z3,z786,z6]),(0,[z0,z787,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z788]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z790,z1,z2,z3,z4,z6]),(0,[z791,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z781,z6]),(0,[z0,z1,z2,z3,z792,z4])],[(0,[z0,z416,z1,z2,z4,z113]),(0,[z793,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z322,z318]),(0,[z0,z1,z2,z3,z252,z232])],[(0,[z0,z1,z2,z3,z4,z794]),(0,[z0,z1,z2,z89,z4,z72]),(0,[z0,z1,z2,z3,z295,z795])],[(0,[z0,z1,z79,z3,z4,z326]),(0,[z0,z99,z2,z27,z4,z23]),(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z1,z2,z3,z253,z367]),(1,[z0,z1,z2,z3,z795])],[(0,[z281,z1,z2,z3,z4,z280]),(0,[z797,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z798,z4,z9]),(0,[z0,z1,z2,z799,z3,z4])],[(0,[z58,z1,z2,z3,z183,z80]),(0,[z119,z1,z74,z3,z4,z38]),(0,[z0,z1,z2,z800,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z801,z6]),(0,[z0,z1,z2,z3,z802,z6]),(0,[z0,z1,z2,z3,z4,z803]),(0,[z0,z1,z2,z3,z90,z9]),(0,[z0,z804,z2,z3,z4,z6]),(0,[z0,z1,z2,z805,z4,z6])],[(0,[z0,z1,z2,z3,z4,z806]),(0,[z0,z1,z290,z3,z4,z23]),(0,[z0,z1,z582,z3,z4,z23]),(0,[z0,z1,z2,z3,z807,z6]),(0,[z808,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z809]),(0,[z0,z1,z2,z65,z4,z92]),(0,[z0,z1,z3,z781,z4,z6])],[(0,[z29,z30,z2,z3,z4,z19]),(0,[z29,z410,z30,z2,z3,z4]),(0,[z29,z466,z30,z2,z3,z4]),(0,[z96,z0,z1,z3,z4,z9])],[(0,[z1,z30,z111,z3,z4,z6]),(0,[z0,z1,z2,z810,z4,z6]),(0,[z0,z1,z2,z811,z4,z6]),(0,[z32,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6]),(0,[z77,z0,z1,z106,z253,z6])],[(0,[z0,z1,z111,z3,z4,z326]),(1,[z812,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z813,z6]),(0,[z0,z1,z457,z3,z45,z4]),(0,[z281,z1,z2,z3,z4,z232]),(0,[z77,z0,z1,z106,z4,z9])],[(0,[z50,z1,z51,z3,z4,z23]),(0,[z58,z1,z2,z3,z167,z6]),(0,[z0,z1,z2,z3,z4,z814]),(0,[z0,z1,z2,z3,z45,z705])],[(0,[z146,z1,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z815]),(0,[z0,z1,z2,z4,z816,z6]),(0,[z0,z1,z2,z3,z4,z817]),(0,[z0,z39,z40,z3,z4,z9]),(0,[z0,z1,z2,z818,z4,z6]),(0,[z77,z0,z135,z106,z4,z6]),(0,[z0,z1,z2,z94,z34,z9])],[(0,[z0,z1,z2,z3,z125,z326]),(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z0,z1,z2,z3,z4,z155]),(0,[z0,z1,z3,z325,z4,z23]),(0,[z46,z0,z1,z3,z4,z9])]],
   [[(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z822,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z67])],[(0,[z304,z0,z1,z2,z3,z23]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z71,z4,z72])],[(0,[z0,z1,z115,z3,z4,z23]),(0,[z0,z1,z2,z824,z4,z6])],[(0,[z0,z1,z79,z3,z4,z6]),(0,[z50,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z825]),(0,[z32,z1,z2,z3,z4,z342]),(0,[z0,z1,z2,z3,z33,z342])],[(0,[z29,z30,z79,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z1,z2,z3,z4,z828]),(0,[z0,z1,z338,z3,z4,z23]),(0,[z0,z1,z137,z3,z66,z234])],[(0,[z0,z1,z2,z3,z829,z6]),(0,[z0,z39,z2,z143,z4,z6])],[(0,[z0,z1,z2,z3,z4,z830]),(0,[z0,z1,z2,z3,z4,z831]),(0,[z0,z832,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z833,z6])],[(0,[z304,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z834,z6])]],
   [[(0,[z0,z835,z1,z2,z3,z4]),(0,[z145,z1,z2,z3,z4,z539]),(0,[z0,z1,z2,z3,z4,z836]),(0,[z837,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z838,z4])],[(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z1,z2,z3,z4,z840])],[(0,[z0,z1,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z841,z6]),(0,[z0,z1,z2,z3,z4,z842]),(0,[z0,z1,z2,z3,z4,z843]),(0,[z844,z1,z2,z3,z4,z6]),(0,[z0,z262,z2,z27,z4,z6]),(0,[z0,z845,z1,z2,z3,z4]),(0,[z41,z0,z2,z3,z4,z846]),(0,[z44,z0,z1,z2,z4,z113])],[(0,[z29,z30,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z1,z355,z3,z4,z23]),(0,[z0,z1,z2,z315,z4,z23]),(0,[z0,z1,z303,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z848]),(0,[z58,z1,z2,z3,z713,z6]),(0,[z0,z849,z2,z3,z4,z6]),(0,[z93,z1,z2,z3,z4,z86])],[(0,[z0,z1,z2,z3,z125,z6]),(0,[z0,z1,z2,z3,z4,z326]),(0,[z0,z1,z2,z3,z4,z850]),(0,[z0,z1,z2,z3,z4,z851]),(0,[z0,z1,z676,z3,z4,z9])],[(0,[z29,z30,z2,z3,z125,z6]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z119,z1,z457,z3,z4,z38]),(0,[z0,z500,z2,z3,z4,z367])],[(0,[z20,z1,z115,z3,z4,z9]),(0,[z0,z1,z2,z3,z322,z23]),(0,[z0,z1,z2,z3,z4,z853]),(0,[z854,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z855,z4]),(0,[z44,z0,z1,z2,z575,z4])]],
   [[(0,[z0,z1,z368,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z856]),(0,[z335,z0,z2,z3,z4,z42]),(0,[z0,z1,z2,z3,z857,z6])],[(0,[z0,z1,z2,z3,z4,z858])],[(0,[z78,z1,z2,z3,z4,z6]),(0,[z0,z1,z774,z3,z4,z6]),(0,[z0,z1,z2,z3,z859,z6]),(0,[z12,z1,z2,z3,z713,z6])],[(0,[z146,z1,z51,z3,z4,z23]),(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z91,z88,z2,z3,z4]),(0,[z0,z1,z2,z861,z4,z6]),(0,[z85,z0,z1,z3,z181,z23])],[(0,[z0,z1,z2,z3,z4,z862]),(1,[z1,z774,z3,z4,z6]),(0,[z278,z0,z2,z3,z16,z6]),(0,[z0,z91,z1,z457,z3,z4]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z2,z3,z4,z42,z846]),(1,[z0,z1,z3,z4,z864]),(0,[z44,z0,z1,z2,z4,z274])],[(0,[z0,z1,z2,z3,z4,z23]),(0,[z20,z304,z1,z2,z3,z6]),(0,[z12,z1,z2,z3,z13,z9]),(0,[z0,z1,z2,z3,z4,z865]),(0,[z0,z1,z555,z3,z4,z23])],[(0,[z0,z1,z2,z866,z4,z6]),(0,[z29,z30,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z252,z23]),(0,[z0,z1,z344,z3,z4,z9])],[(0,[z867,z0,z1,z2,z3,z4]),(0,[z0,z135,z2,z3,z4,z342]),(0,[z0,z1,z26,z868,z4,z6]),(0,[z0,z1,z2,z3,z750,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z869])],[(0,[z0,z1,z2,z870,z4,z6]),(0,[z121,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z871,z4]),(0,[z0,z1,z2,z3,z4,z872]),(0,[z0,z1,z2,z3,z4,z873])],[(0,[z0,z1,z2,z3,z874,z6]),(0,[z0,z1,z2,z3,z4,z875]),(0,[z119,z0,z1,z2,z65,z4]),(0,[z0,z1,z2,z143,z4,z6]),(0,[z78,z1,z2,z3,z4,z342]),(0,[z0,z369,z2,z3,z4,z248])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z79,z213,z4,z6]),(0,[z0,z1,z2,z3,z131,z176]),(0,[z0,z1,z2,z143,z252,z6]),(0,[z0,z1,z2,z3,z4,z876])],[(0,[z0,z452,z2,z27,z4,z6]),(0,[z0,z1,z868,z106,z4,z6])],[(0,[z0,z1,z2,z3,z4,z877])],[(0,[z0,z1,z2,z3,z4,z878]),(0,[z20,z1,z115,z3,z322,z6]),(0,[z0,z1,z74,z3,z4,z23]),(0,[z0,z1,z2,z221,z4,z9]),(0,[z0,z1,z159,z3,z4,z864]),(0,[z0,z1,z3,z4,z23,z653]),(0,[z879,z1,z2,z3,z4,z6])],[(0,[z0,z880,z2,z3,z4,z6]),(0,[z281,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z881]),(0,[z0,z1,z28,z26,z4,z23]),(0,[z882,z1,z2,z3,z4,z6])]],
   [[(0,[z197,z1,z2,z3,z66,z6])],[(0,[z0,z883,z2,z3,z4,z6]),(1,[z1,z2,z755,z4,z6])],[(0,[z0,z1,z111,z213,z4,z6]),(0,[z0,z1,z2,z60,z255,z6]),(0,[z0,z1,z2,z3,z884,z6]),(0,[z0,z1,z410,z388,z2,z3]),(0,[z516,z1,z2,z112,z4,z6]),(0,[z0,z1,z2,z3,z885,z6]),(0,[z0,z1,z2,z3,z886,z4]),(0,[z0,z1,z2,z3,z727,z6])],[(0,[z0,z1,z2,z3,z4,z887]),(0,[z58,z1,z2,z3,z319,z6]),(0,[z888,z1,z2,z3,z4,z6]),(0,[z0,z502,z2,z3,z4,z42])],[(0,[z0,z1,z2,z3,z4,z889]),(0,[z0,z1,z74,z3,z4,z6]),(0,[z12,z1,z2,z3,z638,z6]),(0,[z281,z1,z2,z143,z4,z6]),(0,[z0,z890,z2,z3,z4,z6])],[(0,[z0,z1,z2,z213,z125,z6]),(0,[z0,z891,z1,z2,z3,z4]),(0,[z58,z1,z2,z3,z289,z6]),(0,[z892,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z893,z6])],[(0,[z20,z1,z115,z3,z4,z176]),(0,[z12,z1,z637,z2,z3,z6]),(0,[z0,z1,z28,z868,z4,z6])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z205,z4,z6]),(0,[z0,z39,z40,z3,z4,z14]),(0,[z0,z1,z3,z4,z9,z123]),(0,[z0,z1,z2,z71,z4,z597])]],
   [[(0,[z0,z1,z457,z3,z4,z37]),(0,[z314,z1,z2,z3,z90,z6]),(0,[z895,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z205,z252,z6]),(0,[z32,z1,z2,z3,z253,z6])],[(0,[z0,z1,z2,z60,z4,z19]),(0,[z0,z1,z2,z3,z896,z4]),(0,[z0,z2,z818,z3,z4,z6]),(0,[z32,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z33,z9])],[(0,[z0,z1,z2,z897,z4,z6]),(0,[z0,z1,z2,z3,z4,z898]),(0,[z0,z1,z2,z158,z4,z22]),(0,[z0,z899,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z900]),(0,[z0,z1,z2,z3,z4,z223]),(0,[z0,z1,z2,z3,z45,z795])],[(0,[z0,z1,z901,z3,z4,z6]),(0,[z1,z2,z3,z713,z80,z6]),(0,[z0,z1,z2,z3,z902,z4]),(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z1,z2,z94,z341,z6])],[(0,[z314,z1,z104,z3,z4,z6]),(0,[z904,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z0,z1,z2,z4,z816,z9])],[(0,[z0,z1,z2,z213,z4,z23]),(0,[z119,z1,z2,z3,z556,z4]),(0,[z396,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z4,z908]),(0,[z909,z1,z2,z3,z4,z6]),(0,[z197,z1,z2,z3,z4,z67])],[(0,[z0,z1,z2,z3,z4,z100]),(0,[z0,z910,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z911])],[(0,[z50,z1,z51,z3,z4,z24]),(0,[z211,z1,z2,z282,z4,z6]),(0,[z396,z1,z2,z3,z4,z178]),(0,[z0,z1,z2,z4,z760,z6])]],
   [[(0,[z0,z1,z2,z3,z912,z6]),(0,[z0,z1,z2,z3,z913,z6]),(0,[z0,z1,z461,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z914]),(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z1,z2,z3,z4,z234]),(0,[z0,z1,z2,z141,z4,z72])],[(0,[z0,z1,z79,z3,z4,z9]),(0,[z146,z812,z2,z3,z4,z6]),(0,[z0,z1,z916,z3,z4,z6]),(0,[z0,z1,z2,z629,z4,z113]),(0,[z281,z1,z2,z205,z4,z6]),(0,[z0,z917,z104,z3,z4,z6])],[(0,[z0,z1,z918,z3,z4,z6]),(0,[z185,z0,z104,z143,z4,z6]),(0,[z0,z1,z919,z3,z4,z6]),(0,[z0,z1,z450,z3,z4,z23])],[(0,[z0,z1,z2,z213,z4,z6]),(0,[z50,z1,z774,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z920]),(0,[z185,z0,z104,z3,z4,z6]),(0,[z0,z1,z921,z3,z4,z6]),(0,[z93,z1,z2,z3,z4,z9])],[(0,[z466,z0,z1,z388,z2,z3]),(0,[z185,z0,z104,z3,z252,z6]),(0,[z0,z1,z2,z3,z4,z922]),(0,[z0,z1,z2,z158,z4,z83]),(0,[z85,z0,z1,z3,z781,z6])],[(0,[z0,z1,z2,z3,z923,z6]),(0,[z0,z1,z457,z3,z4,z23]),(0,[z0,z1,z2,z924,z4,z6]),(0,[z0,z1,z2,z3,z4,z925]),(0,[z0,z1,z2,z3,z4,z846]),(0,[z0,z1,z2,z3,z4,z926])],[(0,[z0,z1,z2,z3,z4,z927]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z1,z2,z65,z4,z9]),(0,[z0,z1,z2,z94,z373,z34])],[(0,[z103,z1,z2,z112,z4,z23]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z0,z1,z2,z3,z930,z6])]],
   [[(0,[z0,z1,z111,z3,z4,z9]),(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z77,z0,z1,z106,z4,z367])],[(0,[z600,z1,z115,z3,z4,z6]),(0,[z0,z21,z362,z2,z3,z6]),(0,[z15,z0,z2,z3,z16,z23]),(0,[z0,z1,z933,z3,z4,z6]),(0,[z0,z1,z2,z4,z23,z777])],[(0,[z0,z1,z2,z934,z4,z6]),(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z1,z2,z144,z34,z6]),(0,[z0,z1,z2,z936,z4,z23]),(0,[z44,z0,z1,z2,z4,z760])],[(0,[z0,z1,z2,z3,z125,z9]),(0,[z0,z1,z2,z3,z4,z937]),(0,[z938,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z939]),(0,[z940,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z941]),(0,[z20,z1,z675,z3,z4,z6]),(0,[z0,z1,z2,z942,z4,z6]),(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z135,z2,z3,z253,z6])],[(0,[z0,z1,z944,z3,z4,z6]),(0,[z0,z812,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z135,z2,z3,z4,z9]),(0,[z946,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z94,z161,z34])],[(0,[z0,z1,z2,z3,z4,z277]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z0,z1,z2,z3,z948,z6]),(0,[z0,z99,z2,z27,z4,z6]),(0,[z949,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z70,z403]),(0,[z0,z1,z2,z3,z4,z950])],[(0,[z0,z1,z115,z3,z322,z23]),(0,[z0,z951,z2,z3,z4,z6]),(0,[z0,z1,z2,z952,z4,z6]),(0,[z0,z1,z2,z3,z953,z4]),(0,[z185,z0,z104,z205,z4,z6]),(0,[z954,z1,z2,z3,z4,z6]),(0,[z78,z1,z2,z3,z253,z6])]],
   [[(0,[z0,z1,z955,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z145,z0,z1,z2,z65,z4]),(0,[z0,z1,z2,z957,z4,z6]),(0,[z0,z39,z917,z3,z4,z6]),(0,[z0,z1,z2,z958,z4,z6]),(0,[z78,z1,z2,z3,z4,z9])],[(0,[z0,z1,z2,z3,z4,z959]),(0,[z0,z1,z51,z3,z4,z138]),(0,[z32,z500,z2,z3,z4,z6]),(0,[z0,z500,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z108]),(0,[z85,z0,z1,z3,z181,z67])],[(0,[z1,z115,z51,z3,z4,z23]),(0,[z41,z0,z2,z3,z4,z420]),(0,[z0,z1,z2,z3,z253,z23]),(0,[z197,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z960,z23])],[(0,[z0,z1,z2,z3,z961,z6]),(0,[z314,z1,z40,z3,z4,z6]),(0,[z0,z1,z2,z962,z4,z6]),(0,[z0,z1,z2,z3,z4,z864])],[(0,[z0,z1,z2,z3,z963,z6]),(0,[z0,z506,z2,z27,z4,z6]),(0,[z0,z1,z2,z3,z4,z449]),(0,[z0,z1,z2,z3,z4,z292]),(0,[z0,z2,z134,z27,z4,z6]),(0,[z0,z1,z2,z94,z34,z475])],[(0,[z0,z1,z2,z3,z4,z964]),(0,[z0,z1,z2,z3,z45,z504]),(0,[z0,z1,z3,z171,z4,z9])],[(0,[z197,z1,z2,z3,z181,z6]),(0,[z0,z1,z3,z4,z9,z864])],[(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z1,z2,z3,z966,z6]),(0,[z0,z1,z2,z3,z4,z24]),(0,[z0,z1,z2,z3,z131,z9]),(0,[z0,z1,z2,z3,z967,z6]),(0,[z0,z40,z917,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z968])]],
   [[(0,[z197,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z4,z9]),(0,[z0,z1,z2,z3,z253,z6]),(0,[z0,z1,z2,z3,z960,z6])],[(0,[z0,z1,z2,z3,z4,z9]),(0,[z0,z1,z969,z3,z4,z6]),(0,[z117,z0,z104,z3,z4,z6]),(0,[z187,z0,z1,z2,z4,z113])],[(0,[z0,z1,z2,z3,z255,z19]),(0,[z314,z1,z2,z3,z4,z280])],[(0,[z0,z1,z2,z3,z4,z970]),(0,[z1,z2,z3,z4,z789,z38]),(0,[z77,z32,z1,z106,z4,z6])],[(0,[z0,z1,z2,z3,z971,z6]),(0,[z0,z1,z3,z393,z4,z9])],[(0,[z0,z1,z2,z3,z4,z972])],[(0,[z0,z1,z2,z3,z4,z973]),(0,[z304,z1,z2,z51,z3,z6]),(0,[z0,z1,z51,z3,z4,z449]),(0,[z0,z1,z2,z3,z974,z6]),(0,[z0,z1,z2,z3,z4,z323]),(1,[z0,z2,z3,z4,z846]),(0,[z0,z975,z2,z3,z4,z6])],[(0,[z0,z1,z438,z3,z4,z23])]],
   [[(0,[z642,z1,z51,z3,z4,z6]),(0,[z314,z1,z2,z3,z4,z232]),(0,[z0,z1,z2,z3,z4,z976])],[(0,[z0,z1,z2,z3,z977,z6]),(0,[z29,z30,z2,z3,z4,z326]),(0,[z0,z1,z978,z3,z4,z6]),(0,[z0,z1,z2,z979,z4,z6]),(0,[z0,z99,z2,z27,z4,z100])],[(0,[z980,z1,z2,z3,z4,z6]),(0,[z0,z109,z1,z2,z110,z9])],[(0,[z0,z1,z2,z3,z981,z6])],[(0,[z0,z1,z79,z3,z255,z6]),(0,[z103,z1,z2,z755,z4,z6]),(0,[z0,z491,z2,z3,z4,z92]),(0,[z0,z1,z2,z315,z4,z6]),(0,[z982,z1,z2,z3,z4,z6])],[(0,[z0,z1,z118,z3,z66,z6]),(0,[z0,z1,z2,z3,z295,z670]),(0,[z0,z1,z2,z205,z4,z9]),(0,[z0,z1,z917,z3,z4,z6]),(0,[z0,z1,z663,z3,z4,z9])],[(0,[z58,z1,z51,z3,z4,z23]),(0,[z0,z1,z983,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z984])],[(0,[z0,z1,z2,z985,z3,z4]),(0,[z1,z2,z51,z3,z131,z6]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z0,z1,z2,z3,z4,z987])]],
   [[(0,[z0,z1,z2,z3,z322,z6]),(0,[z0,z1,z2,z3,z988,z6]),(0,[z1,z2,z3,z4,z713,z6]),(0,[z0,z1,z2,z3,z90,z280]),(0,[z78,z500,z2,z3,z4,z6]),(0,[z581,z1,z2,z3,z4,z244]),(0,[z0,z899,z1,z2,z4,z9]),(0,[z0,z1,z2,z750,z4,z6]),(0,[z0,z1,z2,z3,z989,z4])],[(0,[z0,z1,z2,z3,z4,z990]),(0,[z0,z1,z2,z3,z4,z991])],[(0,[z0,z1,z2,z3,z992,z4]),(0,[z1,z774,z51,z3,z4,z6]),(0,[z0,z993,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z994])],[(0,[z0,z1,z111,z3,z255,z6]),(0,[z0,z1,z2,z995,z4,z6]),(0,[z0,z500,z2,z3,z4,z23])],[(0,[z0,z2,z917,z3,z4,z6]),(0,[z0,z91,z2,z3,z4,z248]),(0,[z85,z0,z1,z3,z181,z6])],[(0,[z0,z1,z675,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z996]),(0,[z185,z281,z104,z3,z4,z6]),(0,[z0,z1,z2,z3,z90,z232]),(0,[z0,z1,z997,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z998]),(0,[z0,z2,z818,z27,z4,z6]),(0,[z216,z1,z2,z3,z4,z217])],[(0,[z29,z30,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z178,z23]),(0,[z0,z1,z2,z3,z4,z999]),(0,[z1,z2,z755,z112,z4,z6]),(0,[z0,z1,z2,z3,z252,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z176]),(0,[z495,z1,z2,z112,z4,z6]),(0,[z0,z1,z137,z3,z66,z9]),(0,[z0,z1,z2,z3,z45,z403])],[(0,[z1000,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1001,z6]),(0,[z0,z500,z2,z3,z4,z6]),(0,[z185,z0,z104,z3,z4,z9]),(0,[z0,z1,z2,z3,z4,z1002]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z2,z3,z373,z4]),(0,[z0,z1,z2,z3,z4,z1004])],[(0,[z50,z1,z51,z3,z4,z138]),(0,[z0,z595,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z1005,z4]),(0,[z0,z1,z2,z755,z4,z6]),(0,[z1,z2,z3,z4,z789,z6]),(0,[z197,z85,z1,z3,z181,z6])],[(0,[z0,z1,z79,z3,z4,z1006]),(0,[z1007,z1,z2,z3,z4,z6])],[(0,[z0,z1,z111,z3,z4,z1008])],[(0,[z0,z1,z2,z3,z1009,z6]),(0,[z0,z1,z1010,z2,z3,z4]),(0,[z1011,z0,z1,z2,z3,z4]),(0,[z32,z1,z2,z3,z4,z367]),(0,[z0,z1,z2,z3,z33,z367]),(0,[z0,z1,z3,z868,z4,z6]),(0,[z0,z1,z2,z3,z4,z86]),(0,[z0,z1,z3,z4,z864,z23])],[(0,[z0,z1,z2,z3,z255,z23]),(0,[z0,z1,z2,z3,z4,z342])],[(0,[z146,z147,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1012]),(0,[z0,z1,z115,z3,z4,z138]),(0,[z0,z1,z457,z3,z4,z38]),(0,[z0,z99,z2,z27,z4,z292])]],
   [[(0,[z281,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z213,z4,z326]),(0,[z0,z1,z1013,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1014]),(0,[z0,z1,z2,z3,z1015,z4]),(0,[z0,z1,z28,z26,z4,z6]),(0,[z0,z1,z2,z3,z4,z59]),(0,[z0,z1,z2,z3,z161,z4])],[(0,[z0,z1,z2,z1016,z4,z6]),(0,[z0,z1,z74,z3,z4,z176]),(0,[z0,z1,z457,z3,z4,z113]),(0,[z281,z1,z2,z3,z252,z6]),(0,[z0,z1,z2,z3,z4,z1017]),(0,[z0,z1,z2,z158,z4,z23]),(0,[z77,z0,z1,z868,z4,z6]),(0,[z0,z1,z2,z3,z4,z1018]),(0,[z0,z1,z2,z805,z4,z9])],[(0,[z1,z812,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1019]),(0,[z1,z51,z3,z4,z217,z23]),(0,[z669,z0,z1,z2,z4,z274]),(0,[z0,z1,z2,z3,z4,z795])],[(0,[z0,z1020,z1,z2,z3,z4]),(0,[z0,z1,z1021,z3,z4,z6]),(0,[z211,z1,z2,z173,z4,z23]),(0,[z0,z1,z2,z3,z4,z1022]),(0,[z0,z1,z2,z687,z4,z72]),(0,[z77,z0,z1,z106,z33,z6]),(0,[z1023,z1,z2,z3,z4,z6]),(0,[z0,z109,z1,z2,z750,z6]),(0,[z0,z1,z2,z3,z403,z795])],[(0,[z0,z1,z2,z3,z4,z1024]),(0,[z1025,z1,z2,z3,z4,z6]),(0,[z0,z99,z2,z27,z4,z9])],[(0,[z0,z1,z2,z3,z4,z1026]),(0,[z0,z1,z457,z3,z4,z178]),(0,[z0,z1,z2,z3,z1027,z4]),(0,[z77,z0,z500,z106,z4,z6]),(0,[z0,z1,z2,z1028,z4,z6])],[(0,[z0,z1,z2,z3,z1029,z6]),(0,[z0,z1,z1030,z3,z4,z6]),(1,[z0,z917,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1031])],[(0,[z0,z1,z410,z2,z3,z4]),(0,[z0,z1,z3,z1032,z4,z6]),(0,[z0,z1,z2,z1033,z4,z6]),(0,[z58,z499,z1,z2,z3,z6]),(0,[z0,z1,z2,z1034,z4,z6]),(0,[z1035,z0,z1,z2,z3,z4]),(0,[z187,z0,z1,z2,z4,z168]),(0,[z1036,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z295,z124])]],
   [[(0,[z0,z1,z3,z4,z1037,z23]),(0,[z145,z1,z2,z3,z4,z217]),(0,[z0,z1,z2,z3,z4,z1038])],[(0,[z0,z1,z2,z3,z4,z1039]),(0,[z0,z1,z2,z3,z4,z1040]),(0,[z0,z1,z2,z3,z131,z318]),(0,[z0,z1,z2,z3,z4,z1041]),(0,[z0,z1,z2,z3,z4,z1042]),(0,[z1043,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1044]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z1046,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1047,z6])],[(0,[z0,z1,z2,z1048,z4,z6]),(0,[z314,z1,z2,z3,z4,z23]),(0,[z185,z314,z104,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1049]),(0,[z0,z1,z2,z3,z1050,z4])],[(0,[z0,z1,z2,z1051,z4,z6]),(0,[z50,z1,z51,z3,z4,z9]),(0,[z0,z1,z2,z3,z1052,z6]),(0,[z0,z1,z115,z3,z4,z449]),(0,[z0,z1053,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1054,z4]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z1056,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1008]),(0,[z0,z1,z2,z3,z1057,z6]),(0,[z0,z1,z2,z3,z1058,z4])],[(0,[z0,z1,z79,z60,z4,z6]),(0,[z0,z1,z2,z1059,z3,z6]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z1,z2,z3,z4,z1061]),(0,[z53,z0,z1,z3,z4,z23]),(0,[z0,z1,z2,z3,z1062,z4])],[(0,[z0,z1,z2,z3,z1063,z6]),(0,[z29,z30,z2,z213,z4,z6]),(0,[z0,z1,z1064,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z58,z1,z2,z3,z80,z23]),(0,[z0,z1,z118,z3,z4,z23]),(0,[z0,z1,z2,z3,z1066,z6]),(0,[z1067,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1068,z4]),(0,[z8,z0,z1,z3,z4,z864])]],
   [[(0,[z304,z0,z1,z2,z3,z9]),(0,[z0,z1,z388,z2,z3,z23]),(0,[z1,z115,z774,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1069,z4]),(0,[z1070,z1,z2,z3,z4,z6]),(0,[z0,z135,z2,z3,z4,z367]),(0,[z0,z1,z2,z3,z1071,z4]),(0,[z0,z1,z2,z321,z3,z454]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z1,z2,z3,z4,z760]),(0,[z0,z1,z2,z1073,z4,z6])],[(0,[z0,z1,z2,z3,z4,z138]),(0,[z0,z1,z2,z3,z4,z1074]),(0,[z0,z1,z2,z3,z4,z1075])],[(0,[z58,z1,z2,z3,z497,z6]),(0,[z0,z1,z1076,z3,z4,z6]),(0,[z0,z1,z164,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z1037]),(0,[z1,z51,z3,z112,z4,z23]),(0,[z20,z1,z115,z3,z4,z318]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z78,z1,z2,z3,z4,z367])],[(0,[z0,z1,z111,z60,z4,z6]),(0,[z0,z1,z2,z3,z4,z1078]),(0,[z0,z1,z2,z3,z1079,z4]),(0,[z53,z0,z1,z106,z4,z6]),(0,[z15,z0,z2,z3,z741,z6]),(0,[z0,z2,z3,z4,z846,z6])],[(0,[z0,z1,z2,z3,z1080,z6]),(0,[z0,z1,z457,z3,z4,z6])],[(0,[z0,z1,z79,z3,z4,z730]),(0,[z0,z1,z1081,z3,z4,z6]),(0,[z20,z1,z553,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z60,z125,z6]),(0,[z0,z1,z2,z60,z4,z326]),(0,[z103,z1,z2,z112,z4,z6]),(0,[z1082,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1083]),(0,[z0,z1,z2,z71,z540,z4])],[(0,[z466,z0,z1,z2,z3,z4]),(0,[z1084,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1085]),(0,[z0,z1,z2,z3,z90,z23]),(0,[z1086,z1,z2,z3,z4,z6]),(0,[z1087,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z334,z23])],[(0,[z0,z1,z2,z3,z1088,z6]),(0,[z15,z0,z2,z3,z16,z6]),(0,[z0,z1,z2,z315,z4,z9])],[(0,[z0,z1,z2,z936,z4,z6]),(1,[z0,z1,z2,z750,z6])],[(0,[z0,z324,z2,z27,z4,z6]),(0,[z0,z1,z2,z1089,z4,z6]),(0,[z353,z0,z1,z3,z181,z6]),(0,[z0,z1090,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1091,z6]),(0,[z146,z305,z2,z3,z4,z6]),(0,[z314,z1,z2,z205,z4,z6]),(0,[z1092,z0,z1,z2,z3,z4]),(0,[z77,z0,z1,z106,z4,z23]),(0,[z0,z1,z2,z94,z750,z6])],[(0,[z0,z1,z2,z3,z322,z9]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z0,z1,z573,z26,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z1,z2,z3,z4,z1095]),(0,[z1,z2,z3,z755,z4,z6]),(0,[z0,z1,z2,z1096,z4,z6]),(0,[z1,z2,z3,z4,z37,z789]),(0,[z0,z39,z40,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z1,z2,z94,z34,z23])]],
   [[(0,[z0,z1,z2,z60,z4,z23]),(0,[z0,z1,z3,z4,z651,z23]),(1,[z0,z1,z868,z4,z6]),(0,[z0,z1,z2,z3,z70,z242])],[(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z1,z2,z3,z4,z1099])],[(0,[z85,z0,z1,z3,z181,z9]),(0,[z0,z1,z3,z654,z4,z23])],[(0,[z0,z1,z2,z711,z4,z23]),(0,[z0,z1,z2,z3,z662,z403])],[(0,[z0,z1,z2,z1100,z4,z6]),(0,[z0,z1,z2,z3,z4,z1101])],[(0,[z29,z30,z2,z3,z4,z9]),(0,[z0,z1,z3,z4,z176,z23]),(0,[z0,z39,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1102]),(0,[z0,z1,z2,z3,z252,z9]),(0,[z0,z1,z2,z1103,z4,z6]),(0,[z0,z1,z2,z3,z4,z1104]),(0,[z0,z1,z2,z3,z4,z1105])],[(0,[z0,z1,z2,z60,z4,z6]),(0,[z209,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z4,z1106]),(0,[z0,z1,z2,z1107,z4,z6]),(0,[z0,z1,z28,z26,z4,z108]),(0,[z0,z1,z3,z781,z66,z6]),(0,[z0,z1,z2,z720,z4,z23])],[(0,[z29,z304,z30,z2,z3,z6]),(0,[z0,z1,z2,z3,z45,z406]),(0,[z0,z1,z2,z3,z741,z6]),(0,[z0,z1,z2,z3,z4,z1108]),(0,[z0,z1,z2,z3,z4,z475]),(0,[z0,z1,z2,z3,z635,z124]),(0,[z0,z1,z2,z175,z4,z113])]],
   [[(0,[z0,z1,z493,z3,z4,z23])],[(0,[z0,z1,z2,z1109,z4,z6])],[(0,[z0,z1,z2,z3,z365,z4]),(0,[z0,z180,z2,z3,z4,z92]),(0,[z0,z1,z2,z3,z4,z1110])],[(0,[z0,z1,z2,z1111,z4,z6]),(0,[z1,z774,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1112]),(0,[z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z1113,z3,z4,z6]),(0,[z0,z1,z2,z3,z253,z342])],[(0,[z0,z1,z2,z3,z1114,z6]),(0,[z8,z0,z1,z3,z4,z176]),(0,[z211,z1,z2,z173,z4,z277]),(1,[z1,z2,z3,z713,z6])],[(0,[z0,z1,z2,z3,z4,z1115]),(0,[z0,z1,z2,z3,z4,z1116]),(0,[z286,z1,z2,z3,z80,z6]),(0,[z0,z1,z74,z3,z4,z9]),(0,[z0,z1,z2,z3,z1117,z6]),(0,[z0,z1,z2,z48,z4,z223]),(0,[z0,z1,z1118,z3,z4,z6]),(0,[z0,z400,z2,z3,z4,z92])],[(0,[z0,z1,z2,z3,z1119,z6]),(0,[z0,z1,z1120,z3,z4,z6]),(0,[z0,z1,z3,z4,z9,z477]),(0,[z281,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z1121,z4,z6]),(0,[z0,z1,z28,z26,z4,z9]),(0,[z0,z1,z2,z3,z4,z1122])],[(0,[z0,z91,z2,z221,z4,z92])]],
   [[(0,[z0,z1,z2,z3,z1123,z4]),(0,[z624,z1,z2,z173,z4,z6]),(0,[z0,z1124,z2,z3,z4,z6]),(0,[z1,z2,z3,z13,z713,z6]),(0,[z119,z1,z2,z3,z4,z789]),(0,[z0,z1,z2,z3,z4,z1125]),(0,[z0,z1,z2,z1126,z4,z6]),(0,[z32,z1,z2,z3,z33,z6]),(0,[z254,z1,z2,z3,z4,z334])],[(0,[z0,z1,z2,z48,z4,z100]),(0,[z0,z1,z2,z1127,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z1128]),(0,[z1129,z1,z2,z3,z4,z6])],[(0,[z20,z1,z115,z3,z131,z6]),(0,[z0,z1,z2,z3,z4,z1130])],[(0,[z0,z1,z2,z1131,z4,z6]),(0,[z0,z1,z2,z3,z322,z176]),(0,[z0,z1,z2,z3,z4,z83]),(0,[z1132,z1,z2,z3,z4,z6])],[(0,[z0,z1,z79,z3,z4,z19]),(0,[z12,z1,z2,z3,z13,z23]),(0,[z41,z0,z702,z2,z3,z4]),(0,[z1133,z1,z2,z3,z4,z6])],[(0,[z0,z1,z111,z3,z4,z1134]),(0,[z0,z1,z1135,z3,z4,z6]),(0,[z0,z1,z1136,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1137]),(0,[z185,z0,z104,z3,z90,z6]),(0,[z0,z1,z2,z1138,z4,z6]),(0,[z1139,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1140,z4]),(0,[z0,z1,z2,z259,z4,z72]),(0,[z0,z1,z2,z3,z795,z124])]],
   [[(0,[z0,z1,z553,z3,z4,z23]),(0,[z1141,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z392,z4,z72])],[(0,[z0,z1,z2,z3,z4,z1142]),(0,[z0,z1,z2,z3,z255,z326]),(0,[z0,z1143,z1,z2,z4,z6]),(0,[z147,z812,z2,z3,z4,z6]),(0,[z211,z1,z51,z3,z4,z23])],[(0,[z0,z1,z1144,z3,z4,z6]),(0,[z0,z1,z2,z27,z4,z223]),(0,[z0,z1,z2,z3,z1145,z4]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z1146,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z760,z72])],[(0,[z0,z1,z2,z3,z4,z1147]),(0,[z0,z1,z2,z3,z4,z1148]),(0,[z1149,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z375,z4,z597])],[(0,[z0,z1,z2,z213,z4,z9]),(0,[z618,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1150]),(0,[z0,z1151,z2,z3,z4,z6]),(0,[z211,z1,z2,z173,z4,z323])],[(0,[z0,z1,z111,z3,z4,z19])],[(0,[z0,z1,z1152,z3,z4,z6]),(0,[z0,z1,z2,z3,z1153,z4]),(0,[z0,z1,z2,z3,z1154,z6]),(0,[z49,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z27,z4,z100]),(0,[z85,z0,z1,z3,z181,z86]),(0,[z0,z1,z704,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z1155]),(0,[z304,z466,z0,z1,z2,z3]),(0,[z20,z1,z57,z3,z4,z6]),(0,[z0,z1,z2,z221,z4,z23]),(0,[z0,z1,z2,z3,z4,z1156]),(0,[z93,z1,z2,z3,z4,z67]),(0,[z0,z1,z1157,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z125,z19]),(0,[z0,z1,z2,z143,z4,z280]),(0,[z1158,z1,z2,z3,z4,z6]),(0,[z0,z91,z2,z3,z4,z846]),(0,[z0,z1,z2,z1159,z4,z6])],[(0,[z0,z1,z1160,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1161]),(0,[z0,z1,z2,z3,z4,z1162]),(0,[z0,z1,z2,z3,z4,z280]),(0,[z0,z1,z2,z1163,z4,z6]),(0,[z0,z99,z2,z818,z4,z6]),(0,[z570,z0,z1,z3,z4,z9])],[(0,[z572,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z1164,z6]),(0,[z1165,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1166,z6]),(0,[z0,z135,z2,z26,z4,z6])],[(0,[z15,z0,z659,z2,z3,z6]),(0,[z119,z1,z2,z3,z4,z38]),(0,[z0,z39,z616,z3,z4,z6]),(0,[z0,z1,z2,z426,z4,z72]),(0,[z0,z1,z2,z65,z4,z42]),(0,[z0,z1,z2,z3,z6,z795])],[(0,[z1167,z0,z1,z2,z3,z4]),(0,[z0,z1,z115,z3,z4,z1037]),(0,[z0,z1,z457,z3,z4,z9]),(0,[z0,z1,z2,z3,z4,z1168]),(0,[z32,z135,z2,z3,z4,z6]),(0,[z0,z135,z2,z3,z33,z6]),(0,[z0,z500,z2,z3,z4,z342])],[(0,[z0,z1,z2,z1169,z4,z6]),(0,[z0,z1,z530,z3,z4,z23]),(0,[z0,z1,z35,z3,z4,z9])],[(0,[z0,z1,z1170,z3,z4,z6]),(0,[z103,z1,z2,z112,z4,z9]),(0,[z0,z1,z1171,z3,z4,z6]),(0,[z0,z1,z457,z3,z4,z72]),(0,[z0,z1,z2,z143,z4,z232]),(0,[z640,z0,z2,z3,z16,z6]),(0,[z0,z1,z3,z4,z864,z6])],[(0,[z0,z1,z2,z3,z255,z6]),(0,[z1172,z0,z1,z2,z3,z4]),(0,[z20,z1,z2,z3,z131,z6]),(0,[z0,z1,z2,z1173,z4,z6]),(0,[z0,z1,z2,z3,z4,z232]),(0,[z1,z2,z3,z4,z6,z1174]),(0,[z0,z91,z2,z65,z4,z92]),(0,[z78,z1,z2,z3,z33,z6]),(0,[z1084,z0,z1,z2,z4,z9])]],
   [[(0,[z146,z147,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1134]),(0,[z29,z30,z2,z3,z255,z6]),(0,[z0,z1,z1175,z3,z4,z6]),(1,[z1,z2,z3,z4,z789]),(0,[z145,z590,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z15,z0,z2,z3,z16,z9])],[(0,[z0,z1,z2,z3,z4,z1177]),(0,[z58,z1,z2,z3,z365,z80]),(0,[z0,z2,z3,z4,z846,z92])],[(0,[z0,z1,z79,z3,z125,z6]),(0,[z0,z1,z2,z158,z4,z6]),(0,[z32,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z33,z23]),(0,[z0,z1,z2,z1089,z4,z9]),(0,[z0,z1,z2,z3,z1178,z4]),(0,[z0,z1,z2,z3,z4,z1179])],[(0,[z0,z1,z3,z181,z781,z6])],[(0,[z211,z1,z2,z173,z4,z6]),(0,[z0,z1,z2,z3,z4,z1180])],[(0,[z0,z1,z2,z3,z1181,z4]),(0,[z0,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z205,z4,z280]),(0,[z0,z1,z1182,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1183]),(0,[z0,z1,z28,z26,z4,z59])],[(0,[z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z318]),(0,[z0,z39,z40,z3,z4,z449]),(0,[z0,z1,z2,z3,z4,z1184]),(0,[z0,z1,z2,z3,z4,z1185]),(0,[z0,z1,z2,z3,z4,z1186])],[(0,[z0,z1,z2,z868,z4,z6]),(0,[z0,z1,z612,z3,z4,z23])]],
   [[],[(0,[z0,z1,z111,z3,z125,z6]),(0,[z0,z1,z2,z48,z4,z323]),(0,[z0,z1,z2,z3,z4,z1187]),(0,[z41,z0,z1,z457,z3,z4]),(0,[z0,z1,z2,z3,z253,z9]),(0,[z197,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z295,z454])],[(0,[z0,z1,z79,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1188]),(0,[z0,z1,z2,z3,z1189,z6]),(0,[z185,z0,z917,z3,z4,z6]),(0,[z53,z0,z104,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1190]),(0,[z314,z1,z2,z143,z4,z6]),(0,[z0,z1,z2,z205,z4,z232]),(0,[z0,z1,z2,z3,z43,z371])],[(0,[z0,z1,z2,z60,z4,z9]),(0,[z314,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1191]),(0,[z0,z1,z120,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1192]),(0,[z0,z1,z2,z3,z4,z1193]),(0,[z93,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z1194]),(0,[z29,z812,z2,z3,z4,z6]),(0,[z117,z30,z2,z3,z4,z6]),(0,[z0,z1,z115,z3,z131,z23]),(0,[z581,z1,z2,z3,z4,z38]),(0,[z314,z1,z2,z3,z252,z6])],[(0,[z0,z1,z2,z3,z4,z1006]),(0,[z0,z2,z3,z4,z1195,z6]),(0,[z0,z1,z2,z3,z4,z1196]),(0,[z145,z1,z2,z3,z4,z789]),(0,[z1197,z0,z1,z2,z3,z4]),(0,[z0,z400,z2,z3,z4,z133])],[(0,[z0,z1,z2,z3,z1198,z6]),(0,[z1199,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1200]),(0,[z0,z1,z2,z65,z4,z23])]],
   [[(0,[z0,z1,z2,z1201,z3,z4]),(0,[z58,z1,z2,z3,z80,z6]),(0,[z8,z0,z1,z3,z4,z9])],[(0,[z0,z1,z111,z3,z4,z23]),(0,[z0,z1,z388,z2,z3,z6]),(0,[z185,z0,z104,z3,z4,z280]),(0,[z0,z1,z2,z3,z4,z1202])],[(0,[z0,z1,z2,z3,z4,z1203]),(0,[z93,z1,z2,z3,z4,z6]),(0,[z0,z91,z2,z3,z4,z92]),(1,[z0,z1,z3,z781,z6]),(0,[z0,z1,z2,z110,z750,z6])],[(0,[z812,z30,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1204,z4]),(0,[z0,z1,z2,z3,z4,z1205]),(0,[z78,z135,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z125,z23]),(0,[z0,z1,z1206,z2,z3,z6]),(0,[z0,z1,z2,z3,z1207,z4]),(0,[z0,z1,z2,z1208,z4,z6]),(0,[z0,z1209,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1210]),(0,[z0,z1,z3,z4,z523,z9])],[(0,[z0,z1,z2,z65,z4,z6]),(0,[z0,z1,z2,z3,z4,z1211])],[(0,[z0,z1,z2,z3,z1212,z6]),(0,[z0,z1213,z2,z3,z4,z6]),(0,[z1214,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z27,z4,z323]),(0,[z0,z1,z457,z3,z295,z4]),(0,[z0,z1,z2,z1215,z4,z6]),(0,[z0,z135,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1216])],[(0,[z0,z1,z2,z213,z255,z6]),(0,[z185,z0,z104,z3,z4,z232]),(0,[z0,z455,z2,z3,z4,z42])]],
   [[(0,[z0,z1,z57,z3,z4,z23]),(0,[z0,z1,z356,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z1217]),(0,[z0,z1,z2,z798,z4,z6]),(0,[z0,z1,z2,z3,z1218,z6]),(0,[z0,z1,z2,z3,z4,z367])],[(0,[z0,z1,z2,z3,z1219,z6]),(0,[z0,z1,z508,z3,z4,z23]),(0,[z0,z1,z2,z143,z90,z6]),(0,[z78,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z1220,z4])],[(0,[z0,z1,z1221,z3,z4,z6]),(0,[z0,z1,z2,z3,z90,z6]),(0,[z1222,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z1223]),(0,[z0,z135,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1224]),(0,[z0,z1,z2,z315,z4,z22])],[(0,[z0,z1,z2,z3,z4,z1225]),(0,[z1,z30,z51,z3,z4,z23]),(0,[z304,z0,z1,z410,z2,z3]),(0,[z0,z135,z2,z106,z4,z6])],[(0,[z0,z1,z2,z213,z4,z19]),(0,[z119,z1,z2,z3,z4,z546]),(0,[z1226,z1,z2,z3,z4,z6]),(0,[z0,z1,z299,z3,z66,z6]),(0,[z77,z0,z1,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z1227])],[(0,[z0,z1,z2,z1228,z4,z6]),(0,[z0,z1,z2,z3,z4,z1229]),(0,[z0,z1,z2,z3,z1230,z4]),(0,[z0,z1,z2,z3,z1231,z6]),(0,[z0,z1,z2,z3,z4,z1232]),(0,[z0,z1,z2,z3,z4,z1233])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 524).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1060).take 168) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1228)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [524, 536, 168] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 115).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 115).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 235).take 21).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [115, 120, 21] = true :=
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

end PEqualNP.Outside.L_meta_39259

theorem PEqualNP.Outside.L_meta_39259 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4276680904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4276680904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39259.solve