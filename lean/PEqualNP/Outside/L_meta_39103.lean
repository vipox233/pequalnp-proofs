import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39103

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
  Nat.testBit (4277071584 * 2 ^ 32 + 4209043680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000c321c41711712#64 ++ 0x4000c321c4171171#64 ++ 0xe05c763cc3f33f3f#64 ++ 0xae05c763cc3f33f3#64 : BitVec 256),
   (0x008d82c523144b48#64 ++ 0x8008d82c523144b4#64 ++ 0xb1af8bc7231ccfcf#64 ++ 0x7b1af8bc7231ccfc#64 : BitVec 256),
   (0x26300c028c0aa0a1#64 ++ 0x026300c028c0aa0a#64 ++ 0x6e300c07fc1ff1fe#64 ++ 0xf6e300c07fc1ff1f#64 : BitVec 256),
   (0x4bc00d6836a0fc02#64 ++ 0x04bc00d6836a0fc0#64 ++ 0xefc00ff83fe0fe0d#64 ++ 0xfefc00ff83fe0fe0#64 : BitVec 256),
   (0x1df6d0003bdf000c#64 ++ 0x01df6d0003bdf000#64 ++ 0x5ffff0003fff000b#64 ++ 0xf5ffff0003fff000#64 : BitVec 256),
   (0x8f7b6fb7c0000000#64 ++ 0x08f7b6fb7c000000#64 ++ 0x9fffffffc0000007#64 ++ 0xe9fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [7, 3]⟩, ⟨.and, [9, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c763cc3f33f3f 0xae05c763cc3f33f3

def z1 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8bc7231ccfcf 0x7b1af8bc7231ccfc

def z2 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff404ffff313f 0xf7ffff404ffff313

def z3 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e300c07fc1ff1fe 0xf6e300c07fc1ff1f

def z4 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00ff83fe0fe0d 0xfefc00ff83fe0fe0

def z5 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fffffffc0000007 0xe9fffffffc000000

def z6 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100004c0130132 0x000100004c013013

def z7 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff0003fff000b 0xf5ffff0003fff000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x20200807201cc1ce 0x720200807201cc1c

def z9 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefe00fff3ffcffcf 0xfefe00fff3ffcffc

def z10 : W := mkw 0xafffeff7ef1eebe9 0x8afffeff7ef1eebe 0xffffffffff1fffff 0xfffffffffff1ffff

def z11 : W := mkw 0x000d828501140348 0x8000d82850114034 0x102f8007001c01c2 0x0102f8007001c01c

def z12 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xfffffffffc1ff1ff 0xffffffffffc1ff1f

def z13 : W := mkw 0x143ef214495f031c 0x4143ef214495f031 0x103ff004c01f0132 0x0103ff004c01f013

def z14 : W := mkw 0x4084104837f1ff12 0x44084104837f1ff1 0x600000003ff3ff38 0x1600000003ff3ff3

def z15 : W := mkw 0x4bc00d603680e800 0x04bc00d603680e80 0x0f8009c03c00c000 0x50f8009c03c00c00

def z16 : W := mkw 0x6ff00d6abeaafca3 0x06ff00d6abeaafca 0xeff00fffffffffff 0xfeff00ffffffffff

def z17 : W := mkw 0xaf734da38c0aa0a1 0x0af734da38c0aa0a 0x7fb38dc7fc1ff1fe 0xf7fb38dc7fc1ff1f

def z18 : W := mkw 0x043c321c497b1712 0x4043c321c497b171 0xee7c763cffff3f3f 0xfee7c763cffff3f3

def z19 : W := mkw 0x8f7b6fb7c400a000 0x08f7b6fb7c400a00 0xfffffffffc00f00f 0xffffffffffc00f00

def z20 : W := mkw 0x0084800023140008 0x0008480002314000 0x118f800003000001 0x0118f80000300000

def z21 : W := mkw 0x8f7fefb7c1140348 0x88f7fefb7c114034 0x9fffffffc01c01c7 0xe9fffffffc01c01c

def z22 : W := mkw 0x0bc00d2032800000 0x00bc00d203280000 0xcfc00ff83fe0000d 0xfcfc00ff83fe0000

def z23 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x5fcff0003fe00009 0xf5fcff0003fe0000

def z24 : W := mkw 0x24300002880a00a1 0x024300002880a00a 0x00300007c01f01f2 0x000300007c01f01f

def z25 : W := mkw 0x0084804023144b48 0x80084804023144b4 0x0000000003000e00 0x00000000003000e0

def z26 : W := mkw 0x1df6d0403bdf480c 0x01df6d0403bdf480 0xfffffbc03fffce0f 0xffffffbc03fffce0

def z27 : W := mkw 0x0084804023144b48 0x80084804023144b4 0x20000000231ccfc8 0x120000000231ccfc

def z28 : W := mkw 0x1d72500018cb0004 0x01d72500018cb000 0x5ffff0001ce30003 0xe5ffff0001ce3000

def z29 : W := mkw 0x42000d680420fc02 0x042000d680420fc0 0xa0000ff80000fe04 0x0a0000ff80000fe0

def z30 : W := mkw 0x5ff6dd683ffffc0e 0x05ff6dd683ffffc0 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z31 : W := mkw 0x0004301841711712 0x4000430184171171 0x60507438c3f33f38 0x860507438c3f33f3

def z32 : W := mkw 0x008180c122044848 0x8008180c12204484 0x11a389c3200cc0c0 0x511a389c3200cc0c

def z33 : W := mkw 0x26bd8ec7af1eebe9 0x826bd8ec7af1eebe 0xffbf8fc7ff1fffff 0xfffbf8fc7ff1ffff

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x4040000003e00009 0xa4040000003e0000

def z35 : W := mkw 0x0084804023144808 0x0008480402314480 0xb1af8bc0231cce0f 0x7b1af8bc0231cce0

def z36 : W := mkw 0x4ff24d6836a0fc02 0x04ff24d6836a0fc0 0xfffffff83fe0fe0f 0xffffffff83fe0fe0

def z37 : W := mkw 0x1dffd2c53bdf4b4c 0x81dffd2c53bdf4b4 0xfffffbc73fffcfcf 0xffffffbc73fffcfc

def z38 : W := mkw 0x49cc337c73f15f12 0x449cc337c73f15f1 0x81cc73f803e00e01 0x081cc73f803e00e0

def z39 : W := mkw 0x000902c500004b40 0x8000902c500004b4 0xa0000bc70000cfc4 0x0a0000bc70000cfc

def z40 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xa01c763cc0133f36 0x0a01c763cc0133f3

def z41 : W := mkw 0x1ff6dc02bbdf000c 0x01ff6dc02bbdf000 0x5ffffc07ffff000f 0xf5ffffc07ffff000

def z42 : W := mkw 0x0000301040410010 0x4000030104041001 0x00107000c0030030 0x000107000c003003

def z43 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0x8fc00bf83fe0ce01 0x58fc00bf83fe0ce0

def z44 : W := mkw 0x5ff25d683eebfc06 0x05ff25d683eebfc0 0xefd07ff83fe3fe0d 0xfefd07ff83fe3fe0

def z45 : W := mkw 0x82092fb7c0000000 0x082092fb7c000000 0x80000fffc0000004 0x080000fffc000000

def z46 : W := mkw 0x0009028500000000 0x0000902850000000 0x918f83c000000001 0x0918f83c00000000

def z47 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91cff3f800000001 0x091cff3f80000000

def z48 : W := mkw 0x8fffcfe7a3144b48 0x88fffcfe7a3144b4 0xbfaf8bc7231ccfcf 0x7bfaf8bc7231ccfc

def z49 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fdff7f8c0000001 0x89fdff7f8c000000

def z50 : W := mkw 0x0009028500000000 0x0000902850000000 0x91af8bc700000007 0x691af8bc70000000

def z51 : W := mkw 0x8f726d32c0000000 0x08f726d32c000000 0x0e507438c0000000 0x80e507438c000000

def z52 : W := mkw 0x894341a100000000 0x0894341a10000000 0x118381c000000000 0x0118381c00000000

def z53 : W := mkw 0x108490083bff171e 0x4108490083bff171 0x600000003fff3f38 0x1600000003fff3f3

def z54 : W := mkw 0x008580c123144848 0x8008580c12314484 0x11af89c3231cc0cb 0x711af89c3231cc0c

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100404c0000006 0xa00100404c000000

def z56 : W := mkw 0x26b48c02af1ea0a9 0x026b48c02af1ea0a 0x7fbf8c07ff1ff1ff 0xf7fbf8c07ff1ff1f

def z57 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xbfffffffe01cc1cf 0xfbfffffffe01cc1c

def z58 : W := mkw 0x0b400d2000000000 0x00b400d200000000 0x8fc00ff800000005 0xe8fc00ff80000000

def z59 : W := mkw 0xcffb6ffff6a0fc02 0x0cffb6ffff6a0fc0 0xffffffffffe0fe0f 0xfffffffffffe0fe0

def z60 : W := mkw 0x8f724d2280000000 0x08f724d228000000 0x0e00000000000000 0x00e0000000000000

def z61 : W := mkw 0x1dfef21c7bff171e 0x41dfef21c7bff171 0xdffff2383fff0e0b 0xfdffff2383fff0e0

def z62 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x0e2008033c0cc0c0 0x50e2008033c0cc0c

def z63 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0x9ffffffffc0cc0c7 0xf9ffffffffc0cc0c

def z64 : W := mkw 0x8f7b6ff7c0004b40 0x88f7b6ff7c0004b4 0xbfffffffc000cfc7 0xebfffffffc000cfc

def z65 : W := mkw 0x0080004022004800 0x0008000402200480 0xa1800bc02300ce0d 0x7a1800bc02300ce0

def z66 : W := mkw 0x1d76d00019df000c 0x01d76d00019df000 0x5e7ff0001cff0002 0x85e7ff0001cff000

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e0000003c000008 0xf4e0000003c00000

def z68 : W := mkw 0x49c0004836a0fc02 0x049c0004836a0fc0 0x6fc000003fe0fe09 0xf6fc000003fe0fe0

def z69 : W := mkw 0x843f729fc1711712 0x4843f729fc171171 0xf07ff63fc3f33f3f 0xaf07ff63fc3f33f3

def z70 : W := mkw 0x4bc00d603680e800 0x04bc00d603680e80 0xaf800bc03f00ce0d 0x7af800bc03f00ce0

def z71 : W := mkw 0x3636dc028d5fa0ad 0x03636dc028d5fa0a 0x7e3ffc07fc1ff1fe 0xf7e3ffc07fc1ff1f

def z72 : W := mkw 0x1084900033d5000c 0x01084900033d5000 0x0000000003e00000 0x00000000003e0000

def z73 : W := mkw 0x1d76d000095f000c 0x01d76d000095f000 0x1ffff000001f0003 0xe1ffff000001f000

def z74 : W := mkw 0xaf726d32cc0aa0a1 0x0af726d32cc0aa0a 0x6e707c3ffc1ff1fe 0xf6e707c3ffc1ff1f

def z75 : W := mkw 0x8b4b6fb540000000 0x08b4b6fb54000000 0x9fcffff800000005 0xe9fcffff80000000

def z76 : W := mkw 0x0000301840611412 0x4000030184061141 0x40507438c0e33030 0x840507438c0e3303

def z77 : W := mkw 0x0080000022000000 0x0008000002200000 0x0180000023000009 0x7018000002300000

def z78 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0x81c003f803e00e01 0x081c003f803e00e0

def z79 : W := mkw 0x4bc82f7c76a0ff12 0x44bc82f7c76a0ff1 0xefc00ffcffe0ff3d 0xfefc00ffcffe0ff3

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0x60100404c013313e 0xa60100404c013313

def z81 : W := mkw 0x0004100001510310 0x4000410000151031 0x0000000000130130 0x0000000000013013

def z82 : W := mkw 0x0000004000004b40 0x80000004000004b4 0x200000000000cfc0 0x0200000000000cfc

def z83 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff8073fffc1cf 0xf7ffff8073fffc1c

def z84 : W := mkw 0x4b4c3f3c55f1b712 0x44b4c3f3c55f1b71 0xee5c763cdff33f3f 0xaee5c763cdff33f3

def z85 : W := mkw 0x0000100800611412 0x4000010080061141 0x4000000000e33030 0x04000000000e3303

def z86 : W := mkw 0x8fffeff7e3144b48 0x88fffeff7e3144b4 0xbfffffffe31ccfcf 0xfbfffffffe31ccfc

def z87 : W := mkw 0x1dfef21c7bff171e 0x41dfef21c7bff171 0xfffff63cffff3f3f 0xffffff63cffff3f3

def z88 : W := mkw 0x3ff6dc02bfdfa0ad 0x03ff6dc02bfdfa0a 0x7ffffc07fffff1ff 0xf7ffffc07fffff1f

def z89 : W := mkw 0x5ffeff7c7fffff1e 0x45ffeff7c7fffff1 0xfffffffcffffff3f 0xffffffffcffffff3

def z90 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x1feff0003fec0001 0x51feff0003fec000

def z91 : W := mkw 0x0008221440000000 0x0000822144000000 0x805c763cc0000007 0xa805c763cc000000

def z92 : W := mkw 0x8f734da380000000 0x08f734da38000000 0x1fa389c300000000 0x41fa389c30000000

def z93 : W := mkw 0x1d72500018cb0004 0x01d72500018cb000 0x4e5070001ce30000 0x84e5070001ce3000

def z94 : W := mkw 0x06300c0280000000 0x006300c028000000 0x0e300c07c0000006 0xe0e300c07c000000

def z95 : W := mkw 0x0008020400000300 0x0000802040000030 0xa000020400000f04 0x0a000020400000f0

def z96 : W := mkw 0x0000000800201402 0x0000000080020140 0x6000000003e03e08 0x06000000003e03e0

def z97 : W := mkw 0x843b6297c0000000 0x0843b6297c000000 0x907ff63fc0000007 0xa907ff63fc000000

def z98 : W := mkw 0xaf726d32cc0aa0a1 0x0af726d32cc0aa0a 0x4e507438dc033030 0x84e507438dc03303

def z99 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x11cff00003e00001 0x011cff00003e0000

def z100 : W := mkw 0x1df2c0003a8e000c 0x01df2c0003a8e000 0x1fa380003c0c0000 0x51fa380003c0c000

def z101 : W := mkw 0x008d82cd23345f4a 0x8008d82cd23345f4 0xf1ef8fff23fcffcf 0xff1ef8fff23fcffc

def z102 : W := mkw 0x4b400d2814a0b402 0x04b400d2814a0b40 0x4e4004381ce03000 0x84e4004381ce0300

def z103 : W := mkw 0x4bc90fed36a0fc02 0x04bc90fed36a0fc0 0xffef8fff3fe0fe0f 0xfffef8fff3fe0fe0

def z104 : W := mkw 0x008180c122044848 0x8008180c12204484 0x31a389c7201cc1ce 0x731a389c7201cc1c

def z105 : W := mkw 0x0000000800201402 0x0000000080020140 0xe040063803e03e0d 0xae040063803e03e0

def z106 : W := mkw 0x5ff6dd603fdfe80c 0x05ff6dd603fdfe80 0x5ffff9c03fffc00b 0xf5ffff9c03fffc00

def z107 : W := mkw 0x0000301840611412 0x4000030184061141 0xe0507638c3e33e3d 0xae0507638c3e33e3

def z108 : W := mkw 0x800b629540000000 0x0800b62954000000 0x100ff00000000000 0x0100ff0000000000

def z109 : W := mkw 0x1df2c0003a8e000c 0x01df2c0003a8e000 0x5fb380003c1f000a 0xf5fb380003c1f000

def z110 : W := mkw 0x0008321c40611712 0x40008321c4061171 0xe050763cc0e33f34 0x8e050763cc0e33f3

def z111 : W := mkw 0x0084800023140008 0x0008480002314000 0x00000000231c0008 0x100000000231c000

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008070000c1c4 0x0200008070000c1c

def z113 : W := mkw 0x108490003bdf000c 0x0108490003bdf000 0x400000003fff0008 0x1400000003fff000

def z114 : W := mkw 0x9fffffb7fbdf000c 0x09fffffb7fbdf000 0xdfffffffffff000f 0xfdfffffffffff000

def z115 : W := mkw 0x0004100801711712 0x4000410080171171 0x605c700003f33f3b 0xa605c700003f33f3

def z116 : W := mkw 0x26390ec78c0aebe1 0x826390ec78c0aebe 0xee300fc7fc1ffffe 0xfee300fc7fc1ffff

def z117 : W := mkw 0x02000c0280000000 0x002000c028000000 0x00000c07c0000004 0x000000c07c000000

def z118 : W := mkw 0x4080004836a0fc02 0x04080004836a0fc0 0x600000003fe0fe08 0x1600000003fe0fe0

def z119 : W := mkw 0x1006d0000155000c 0x01006d0000155000 0x100ff00000000000 0x0100ff0000000000

def z120 : W := mkw 0x4080004832a05c02 0x04080004832a05c0 0x0000000003e00e00 0x00000000003e00e0

def z121 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x302f8007231ccfca 0x1302f8007231ccfc

def z122 : W := mkw 0x0084900023550008 0x0008490002355000 0x51fff00023ff000b 0xf51fff00023ff000

def z123 : W := mkw 0x4bcc3f7c77f1ff12 0x44bcc3f7c77f1ff1 0xefdc7ffcfff3ff3f 0xfefdc7ffcfff3ff3

def z124 : W := mkw 0x24300002880a00a1 0x024300002880a00a 0x60300407c01f31fe 0xa60300407c01f31f

def z125 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91effbff00000007 0x691effbff0000000

def z126 : W := mkw 0x000902c500004b40 0x8000902c500004b4 0xb1af8bc70000cfc7 0x6b1af8bc70000cfc

def z127 : W := mkw 0x24bd82c7ab1e4be9 0x824bd82c7ab1e4be 0xb1bf8bc7e31fcfff 0x7b1bf8bc7e31fcff

def z128 : W := mkw 0xcff34debb6a0fc02 0x0cff34debb6a0fc0 0xffe38ffb3fe0fe0d 0xfffe38ffb3fe0fe0

def z129 : W := mkw 0x508490483ffffc0e 0x0508490483ffffc0 0x600000003ffffe08 0x1600000003ffffe0

def z130 : W := mkw 0x0008221c40201712 0x40008221c4020171 0xa000063cc0003f34 0x0a000063cc0003f3

def z131 : W := mkw 0x8f7f7fbfc1711712 0x48f7f7fbfc171171 0xffffffffc3f33f3f 0xeffffffffc3f33f3

def z132 : W := mkw 0x20000000080a00a1 0x020000000080a00a 0x00000000001f01f0 0x000000000001f01f

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200007001c01c2 0x000200007001c01c

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020080700000006 0x6002008070000000

def z135 : W := mkw 0x6bc00d6ab6a0fca3 0x06bc00d6ab6a0fca 0xefc00fffffe0fffd 0xfefc00fffffe0fff

def z136 : W := mkw 0x06300c028400a000 0x006300c028400a00 0x6e300c07fc00f00e 0xf6e300c07fc00f00

def z137 : W := mkw 0x24300002880a00a1 0x024300002880a00a 0x00100000c0030030 0x000100000c003003

def z138 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0x805c723cc3f30f33 0x0805c723cc3f30f3

def z139 : W := mkw 0x0d724000080a0000 0x00d724000080a000 0x5ffff0003c1f000b 0xf5ffff0003c1f000

def z140 : W := mkw 0x263c3e1ecd7bb7b3 0x4263c3e1ecd7bb7b 0xee7c7e3fffffffff 0xfee7c7e3ffffffff

def z141 : W := mkw 0x4b400d2814a0b402 0x04b400d2814a0b40 0xee4006381fe03e0d 0xaee4006381fe03e0

def z142 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e100c07dc03f1f4 0x86e100c07dc03f1f

def z143 : W := mkw 0x4000016800205c02 0x04000016800205c0 0x800003f800000e00 0x0800003f800000e0

def z144 : W := mkw 0x6ff00d62be8ae8a1 0x06ff00d62be8ae8a 0x0fa009c33c0cc0c0 0x50fa009c33c0cc0c

def z145 : W := mkw 0x894f73bd41711712 0x4894f73bd4171171 0xf1dff7fcc3f33f3f 0xaf1dff7fcc3f33f3

def z146 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0x804c723803e00e01 0x0804c723803e00e0

def z147 : W := mkw 0x000d82c501144b48 0x8000d82c501144b4 0xb02f8bc7001ccfc6 0x0b02f8bc7001ccfc

def z148 : W := mkw 0x19c490003bdf000c 0x019c490003bdf000 0x4fc000003fff0009 0xf4fc000003fff000

def z149 : W := mkw 0x008db2dd63755f5a 0xc008db2dd63755f5 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z150 : W := mkw 0x0b400d2800201402 0x00b400d280020140 0xefc00ff803e03e0d 0xeefc00ff803e03e0

def z151 : W := mkw 0x36b49c02bfdfa0ad 0x036b49c02bfdfa0a 0x6e300c07fffff1fe 0xf6e300c07fffff1f

def z152 : W := mkw 0x000000000400a000 0x0000000000400a00 0x600000003c00f008 0x1600000003c00f00

def z153 : W := mkw 0x0004100001510000 0x0000410000151000 0x405c700003f3000b 0xa405c700003f3000

def z154 : W := mkw 0x008d92c523554b48 0x8008d92c523554b4 0xf1fffbc723ffcfcf 0xff1fffbc723ffcfc

def z155 : W := mkw 0x9ffbefb7fa8e000c 0x09ffbefb7fa8e000 0x9ffffffffc0c0007 0xf9ffffffffc0c000

def z156 : W := mkw 0x04300000080a0000 0x004300000080a000 0x4e1000001c030000 0x84e1000001c03000

def z157 : W := mkw 0x000c020401100300 0x0000c02040110030 0xe01c0604c3133f3f 0xae01c0604c3133f3

def z158 : W := mkw 0x22090ec78400ebe1 0x822090ec78400ebe 0xa0000fc7c000fff4 0x0a0000fc7c000fff

def z159 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x2e2008073c1cc1ce 0x72e2008073c1cc1c

def z160 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x1fbff9c7c0000002 0x41fbff9c7c000000

def z161 : W := mkw 0x008db2d563554b58 0xc008db2d563554b5 0xb1bffbc7e31fcfff 0x7b1bffbc7e31fcff

def z162 : W := mkw 0x4bcd8fed37b4ff4a 0x84bcd8fed37b4ff4 0xffef8fff3ffcffcf 0xfffef8fff3ffcffc

def z163 : W := mkw 0x8d7b63b7c0000000 0x08d7b63b7c000000 0x91fff3ffc0000003 0x091fff3ffc000000

def z164 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91dff7fcc0000007 0xa91dff7fcc000000

def z165 : W := mkw 0x1d724000188a0004 0x01d724000188a000 0x0e0000001c000000 0x00e0000001c00000

def z166 : W := mkw 0x0009229540000000 0x0000922954000000 0x91ffffffc0000007 0xe91ffffffc000000

def z167 : W := mkw 0x1df6d0083bff140e 0x01df6d0083bff140 0xfffff6383fff3e0f 0xffffff6383fff3e0

def z168 : W := mkw 0x82092fbfc0201712 0x482092fbfc020171 0xa0000fffc0003f34 0x0a0000fffc0003f3

def z169 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x918f83c003000e01 0x0918f83c003000e0

def z170 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e100400dc033030 0x84e100400dc03303

def z171 : W := mkw 0xcf7b6fbfd4a0b402 0x0cf7b6fbfd4a0b40 0xdfffffffdce03007 0xedfffffffdce0300

def z172 : W := mkw 0x22000c028c0aa0a1 0x022000c028c0aa0a 0x60000c07fc1ff1fc 0x160000c07fc1ff1f

def z173 : W := mkw 0xa43b6297c80a00a1 0x0a43b6297c80a00a 0x103ff007c01f01f2 0x0103ff007c01f01f

def z174 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af8bc3230ccec1 0x591af8bc3230ccec

def z175 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9feffbfb00000001 0x49feffbfb0000000

def z176 : W := mkw 0x0008221440000000 0x0000822144000000 0x804c723800000001 0x0804c72380000000

def z177 : W := mkw 0x0d72400000000000 0x00d7240000000000 0x1ffff00000000003 0xe1ffff0000000000

def z178 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x6e000c003c00f00c 0xf6e000c003c00f00

def z179 : W := mkw 0x49cc337c73f15f12 0x449cc337c73f15f1 0xe1dc77fcc3f33f3f 0xae1dc77fcc3f33f3

def z180 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x51dff00003f3000b 0xa51dff00003f3000

def z181 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0xa1c00bf823e0ce0d 0x7a1c00bf823e0ce0

def z182 : W := mkw 0x09cc321c73f11712 0x409cc321c73f1171 0xefdc763cfff33f3f 0xfefdc763cfff33f3

def z183 : W := mkw 0x3df6d002bbdf00ad 0x03df6d002bbdf00a 0x5ffff007ffff01fb 0xf5ffff007ffff01f

def z184 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0x805c763cc3e00e07 0xa805c763cc3e00e0

def z185 : W := mkw 0x200000000400a0a1 0x0200000000400a0a 0x200000000000f1f0 0x0200000000000f1f

def z186 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0x4fc00df83ce0f000 0xd4fc00df83ce0f00

def z187 : W := mkw 0xaf7b6fb7c80a00a1 0x0af7b6fb7c80a00a 0x9fffffffc01f01f7 0xe9fffffffc01f01f

def z188 : W := mkw 0x008982c522044b48 0x8008982c522044b4 0xb1a38bc7200ccfc4 0x5b1a38bc7200ccfc

def z189 : W := mkw 0x4bcd8fe53794eb48 0x84bcd8fe53794eb4 0xbfaf8bc73f1ccfcf 0x7bfaf8bc73f1ccfc

def z190 : W := mkw 0x400000480420fc02 0x0400000480420fc0 0x200000000000fe00 0x0200000000000fe0

def z191 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xc05c7638c3e33e31 0x8c05c7638c3e33e3

def z192 : W := mkw 0x22000c028400a0a1 0x022000c028400a0a 0x20000c07c000f1f4 0x020000c07c000f1f

def z193 : W := mkw 0x9f7fffb7c95f000c 0x09f7fffb7c95f000 0x9fffffffc01f0007 0xe9fffffffc01f000

def z194 : W := mkw 0x8f7b6fbfc0201712 0x48f7b6fbfc020171 0xbfffffffc0003f37 0xebfffffffc0003f3

def z195 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af83c7031c0fc3 0x091af83c7031c0fc

def z196 : W := mkw 0x0004100001510000 0x0000410000151000 0x004c700003e00001 0x0004c700003e0000

def z197 : W := mkw 0x4bc00d603680e800 0x04bc00d603680e80 0x6f800dc03c00f00c 0xf6f800dc03c00f00

def z198 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x6e200c073c1cf1ce 0xf6e200c073c1cf1c

def z199 : W := mkw 0x8f7e7f3ec1711712 0x48f7e7f3ec171171 0xee5c763cc3f33f3f 0xaee5c763cc3f33f3

def z200 : W := mkw 0x8f727d3ac0611412 0x48f727d3ac061141 0x4e507438c0e33030 0x84e507438c0e3303

def z201 : W := mkw 0x26b00c42ae0ae8a1 0x026b00c42ae0ae8a 0xefb00fc7ff1fffff 0xfefb00fc7ff1ffff

def z202 : W := mkw 0xdffffffffffffc0e 0x0dffffffffffffc0 0xfffffffffffffe0f 0xffffffffffffffe0

def z203 : W := mkw 0x06300c0280000000 0x006300c028000000 0x2e300c07e01cc1ce 0xf2e300c07e01cc1c

def z204 : W := mkw 0x0080004022004800 0x0008000402200480 0xa1a00bc7231ccfcf 0x7a1a00bc7231ccfc

def z205 : W := mkw 0xc9cb63fd72a05c02 0x0c9cb63fd72a05c0 0x91cff3f803e00e01 0x091cff3f803e00e0

def z206 : W := mkw 0x4b400d2814a0b402 0x04b400d2814a0b40 0x6e400c383ce0f00c 0xf6e400c383ce0f00

def z207 : W := mkw 0x09c0000032800000 0x009c000003280000 0x01c0000003e00001 0x001c0000003e0000

def z208 : W := mkw 0x10049000095f000c 0x010049000095f000 0x00000000001f0000 0x000000000001f000

def z209 : W := mkw 0x42800c4836a0fc02 0x042800c4836a0fc0 0x6e000c003fe0fe0c 0xf6e000c003fe0fe0

def z210 : W := mkw 0x8f7b4fa780000000 0x08f7b4fa78000000 0x9faf8bc700000007 0x69faf8bc70000000

def z211 : W := mkw 0x0008221c40201712 0x40008221c4020171 0x8000023800000e00 0x08000023800000e0

def z212 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0xe1c007f803e03e0d 0xae1c007f803e03e0

def z213 : W := mkw 0x008cb21c6375171a 0x4008cb21c6375171 0xf1fff63ce3ff3f3f 0xff1fff63ce3ff3f3

def z214 : W := mkw 0x8ffb6ff7e2004800 0x08ffb6ff7e200480 0xbfffffffe300ce0f 0xfbfffffffe300ce0

def z215 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0xcfc003f83fe00e09 0xfcfc003f83fe00e0

def z216 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x11fff00003ff0003 0x011fff00003ff000

def z217 : W := mkw 0x800923b540000000 0x0800923b54000000 0x800003f800000000 0x0800003f80000000

def z218 : W := mkw 0x1ff6dc003fdfa00c 0x01ff6dc003fdfa00 0x7ffffc003ffff00f 0xf7ffffc003ffff00

def z219 : W := mkw 0x0940012000000000 0x0094001200000000 0x81c003f800000001 0x081c003f80000000

def z220 : W := mkw 0x0000201040000000 0x0000020104000000 0x00507438c0000000 0x800507438c000000

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008002000c00c 0x7200008002000c00

def z222 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x4e0004001c003000 0x84e0004001c00300

def z223 : W := mkw 0x3f725c029ccba0a5 0x03f725c029ccba0a 0x6e707c07fcfff1fe 0xf6e707c07fcfff1f

def z224 : W := mkw 0xcbc92ffff6a0fc02 0x0cbc92ffff6a0fc0 0xefc00fffffe0fe0d 0xfefc00fffffe0fe0

def z225 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xffffffffc013313f 0xeffffffffc013313

def z226 : W := mkw 0x14b6d0002b5f000c 0x014b6d0002b5f000 0x11bff000231f000b 0x711bff000231f000

def z227 : W := mkw 0x0942400000000000 0x0094240000000000 0x11cff00000000001 0x011cff0000000000

def z228 : W := mkw 0x3df6d0003fdfa0ad 0x03df6d0003fdfa0a 0x7ffff0003ffff1fb 0xf7ffff0003ffff1f

def z229 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x2e200c07fc0cf1f4 0x52e200c07fc0cf1f

def z230 : W := mkw 0x06300c0280000000 0x006300c028000000 0x0e100400c0000000 0x80e100400c000000

def z231 : W := mkw 0x000d329d41711712 0x4000d329d4171171 0xf1ffffffc3f33f3f 0xef1ffffffc3f33f3

def z232 : W := mkw 0x000c321441510310 0x4000c32144151031 0x405c7004c3f3013b 0xa405c7004c3f3013

def z233 : W := mkw 0x0004100801711712 0x4000410080171171 0x60100404c3f33f3e 0xa60100404c3f33f3

def z234 : W := mkw 0x408c325c77f1ff12 0x4408c325c77f1ff1 0xe05c763cfff3ff3f 0xbe05c763cfff3ff3

def z235 : W := mkw 0x0004100801711712 0x4000410080171171 0x0000000003e00e00 0x00000000003e00e0

def z236 : W := mkw 0x0084800023140008 0x0008480002314000 0x11af8000231c000b 0x711af8000231c000

def z237 : W := mkw 0x0008020400000000 0x0000802040000000 0x800c020400000007 0x2800c02040000000

def z238 : W := mkw 0x22000c028400a0a1 0x022000c028400a0a 0x000008030000c0c0 0x0000008030000c0c

def z239 : W := mkw 0x1436d000095f000c 0x01436d000095f000 0x103ff000001f0002 0x0103ff000001f000

def z240 : W := mkw 0x06382e16c0000000 0x006382e16c000000 0x8e7c7e3fc0000007 0xe8e7c7e3fc000000

def z241 : W := mkw 0x008180c122044848 0x8008180c12204484 0xb1a38bc3230ccecd 0x7b1a38bc3230ccec

def z242 : W := mkw 0x8f726d32c0000000 0x08f726d32c000000 0x1ffff438c0000003 0xe1ffff438c000000

def z243 : W := mkw 0x22000c028400a0a1 0x022000c028400a0a 0x20200c07e01cf1fe 0x720200c07e01cf1f

def z244 : W := mkw 0x8b4b6fb7c0000000 0x08b4b6fb7c000000 0x91cfffffc0000005 0x091cfffffc000000

def z245 : W := mkw 0x000922dd40205f52 0xc000922dd40205f5 0xa0000fffc000fff4 0x0a0000fffc000fff

def z246 : W := mkw 0x0000000800201402 0x0000000080020140 0x4040043800e03000 0x84040043800e0300

def z247 : W := mkw 0x5f725d281cebb406 0x05f725d281cebb40 0x4e5074381ce33000 0x84e5074381ce3300

def z248 : W := mkw 0x8f726d32c0000000 0x08f726d32c000000 0x0e707c3fc0000006 0xe0e707c3fc000000

def z249 : W := mkw 0x04300000080a0000 0x004300000080a000 0x4e3000003c1f000a 0xf4e3000003c1f000

def z250 : W := mkw 0x3ff6dc02bfdfa0ad 0x03ff6dc02bfdfa0a 0x5ffff400ffff303b 0xf5ffff400ffff303

def z251 : W := mkw 0x09c0000032800000 0x009c000003280000 0x4fc000003fe00009 0xf4fc000003fe0000

def z252 : W := mkw 0x0008221c40201712 0x40008221c4020171 0xa05c763cc0003f37 0xaa05c763cc0003f3

def z253 : W := mkw 0x200000000c0aa0a1 0x0200000000c0aa0a 0x600000003c1ff1f8 0x1600000003c1ff1f

def z254 : W := mkw 0x0004100001510000 0x0000410000151000 0x001c700000130002 0x0001c70000013000

def z255 : W := mkw 0x1dfef2147bdf000c 0x01dfef2147bdf000 0xdffff63cffff000f 0xfdffff63cffff000

def z256 : W := mkw 0x8ff3cde3a2044848 0x88ff3cde3a204484 0x1fa389c3200cc0c0 0x51fa389c3200cc0c

def z257 : W := mkw 0x8942613040000000 0x0894261304000000 0x0040703800000000 0x0004070380000000

def z258 : W := mkw 0x4bc90fed36a0ff42 0x84bc90fed36a0ff4 0xefc00fff3fe0ffcd 0xfefc00fff3fe0ffc

def z259 : W := mkw 0x80092297c0000000 0x080092297c000000 0x00000007c0000000 0x000000007c000000

def z260 : W := mkw 0x5fffdfed3fffff4e 0x85fffdfed3fffff4 0xffffffff3fffffcf 0xfffffffff3fffffc

def z261 : W := mkw 0xaf7b6fb7c400a0a1 0x0af7b6fb7c400a0a 0xbfffffffc000f1f7 0xebfffffffc000f1f

def z262 : W := mkw 0x49c0016836a0fc02 0x049c0016836a0fc0 0xe1c003f83fe0fe09 0x1e1c003f83fe0fe0

def z263 : W := mkw 0x1df6f0187bff141e 0x41df6f0187bff141 0x5ffff438ffff303b 0xf5ffff438ffff303

def z264 : W := mkw 0x1436d000095f000c 0x01436d000095f000 0x507ff00003ff000b 0xa507ff00003ff000

def z265 : W := mkw 0x82092ff7c0004b40 0x882092ff7c0004b4 0xa0000fffc000cfc4 0x0a0000fffc000cfc

def z266 : W := mkw 0x3436d002895f00ad 0x03436d002895f00a 0x103ff007c01f01f2 0x0103ff007c01f01f

def z267 : W := mkw 0x608000483eaafca3 0x0608000483eaafca 0x600000003ffffff8 0x1600000003ffffff

def z268 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0x601c7004c3f33f3a 0x0601c7004c3f33f3

def z269 : W := mkw 0x000c020401100300 0x0000c02040110030 0xa00c020403100f0f 0x2a00c020403100f0

def z270 : W := mkw 0x1dfff2dd7bff5f5e 0xc1dfff2dd7bff5f5 0xffffffffffffffff 0xffffffffffffffff

def z271 : W := mkw 0x26bd8ec7af1eebe9 0x826bd8ec7af1eebe 0xbfaf8bc73f1ccfcf 0x7bfaf8bc73f1ccfc

def z272 : W := mkw 0xcffb6ff7f680e800 0x0cffb6ff7f680e80 0x9ffffffffc00c007 0xf9ffffffffc00c00

def z273 : W := mkw 0x0d76500001510000 0x00d7650000151000 0x5ffff00003f3000b 0xe5ffff00003f3000

def z274 : W := mkw 0x14b490003bdf000c 0x014b490003bdf000 0x4e3000003fff000a 0xf4e3000003fff000

def z275 : W := mkw 0x4080004836a0fc02 0x04080004836a0fc0 0xe04006383fe0fe0d 0xbe04006383fe0fe0

def z276 : W := mkw 0x000c321441510310 0x4000c32144151031 0x001c7004c0130132 0x0001c7004c013013

def z277 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe07c7e3fe3ffffff 0xfe07c7e3fe3fffff

def z278 : W := mkw 0xcfffeffff7b4ff4a 0x8cfffeffff7b4ff4 0xfffffffffffcffcf 0xffffffffffffcffc

def z279 : W := mkw 0x0df6c00023140008 0x00df6c0002314000 0x1ffff000231c000b 0xf1ffff000231c000

def z280 : W := mkw 0x8fffffffe3755f5a 0xc8fffffffe3755f5 0xffffffffe3ffffff 0xfffffffffe3fffff

def z281 : W := mkw 0x4bcdbffd77f5ff5a 0xc4bcdbffd77f5ff5 0xffffffffffffffff 0xffffffffffffffff

def z282 : W := mkw 0x0080800022040008 0x0008080002204000 0x11a38000200c0000 0x511a38000200c000

def z283 : W := mkw 0x1432c000080e000c 0x01432c000080e000 0x10238000000c0000 0x010238000000c000

def z284 : W := mkw 0x4b400d680420fc02 0x04b400d680420fc0 0xafc00ff80000fe05 0xeafc00ff80000fe0

def z285 : W := mkw 0x4b403d3854e1b412 0x44b403d3854e1b41 0x4e507438dce33030 0x84e507438dce3303

def z286 : W := mkw 0x26390e878c0aa0a1 0x026390e878c0aa0a 0xffbf8fc7fc1ff1ff 0xfffbf8fc7fc1ff1f

def z287 : W := mkw 0x4b400d201480a000 0x04b400d201480a00 0x0e0000001c000000 0x00e0000001c00000

def z288 : W := mkw 0x0000100000410000 0x0000010000041000 0x4050700000e30000 0x84050700000e3000

def z289 : W := mkw 0x863b6fb7c0000000 0x0863b6fb7c000000 0x903fffffc0000006 0x0903fffffc000000

def z290 : W := mkw 0x66300d6a8c2afca3 0x066300d6a8c2afca 0xee300ffffc1ffffe 0xfee300ffffc1ffff

def z291 : W := mkw 0x428d8fed2734ff4a 0x8428d8fed2734ff4 0xb1af8fff231cffcf 0x7b1af8fff231cffc

def z292 : W := mkw 0x9dfff3b57bdf000c 0x09dfff3b57bdf000 0xdffff3f83fff000b 0xfdffff3f83fff000

def z293 : W := mkw 0x9dfff297fbdf000c 0x09dfff297fbdf000 0x5ffff007ffff000b 0xf5ffff007ffff000

def z294 : W := mkw 0x4ff00d683eaafc02 0x04ff00d683eaafc0 0xeff00ff83ffffe0f 0xfeff00ff83ffffe0

def z295 : W := mkw 0x9fffffb7f3d5000c 0x09fffffb7f3d5000 0x9fffffffc3e00007 0xe9fffffffc3e0000

def z296 : W := mkw 0x8d7b63b540000000 0x08d7b63b54000000 0x9ffff3f800000003 0xe9ffff3f80000000

def z297 : W := mkw 0x0bcd8fe523144b48 0x80bcd8fe523144b4 0xbfef8fff231ccfcf 0xfbfef8fff231ccfc

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000040010010e 0x2200000040010010

def z299 : W := mkw 0x0001008100000000 0x0000100810000000 0x11a389c300000000 0x411a389c30000000

def z300 : W := mkw 0x1dffd2c53bdf4b4c 0x81dffd2c53bdf4b4 0xdffff3c03fff0e0b 0xfdffff3c03fff0e0

def z301 : W := mkw 0x0000000800201402 0x0000000080020140 0xe050063cc3f33f3f 0xae050063cc3f33f3

def z302 : W := mkw 0x49cd83ed33b45f4a 0x849cd83ed33b45f4 0xb1ef8bff23fccfcf 0x7b1ef8bff23fccfc

def z303 : W := mkw 0x4bc03d7876e1fc12 0x44bc03d7876e1fc1 0xefd07ff8ffe3fe3d 0xfefd07ff8ffe3fe3

def z304 : W := mkw 0x26382e1ecc2ab7b3 0x426382e1ecc2ab7b 0xee300e3ffc1ffffe 0xfee300e3ffc1ffff

def z305 : W := mkw 0x06390e8780000000 0x006390e878000000 0x9fbf8fc7c0000007 0xe9fbf8fc7c000000

def z306 : W := mkw 0x0000000800201712 0x4000000080020171 0x2000000000003f30 0x02000000000003f3

def z307 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0x6e4004383fe0fe08 0x96e4004383fe0fe0

def z308 : W := mkw 0xc2092fffc420fc02 0x0c2092fffc420fc0 0xa0000fffc000fe04 0x0a0000fffc000fe0

def z309 : W := mkw 0x8f7b6fbfc0201402 0x08f7b6fbfc020140 0xffffffffc3e03e0f 0xeffffffffc3e03e0

def z310 : W := mkw 0x0000301840611412 0x4000030184061141 0x6050743cc0f3313e 0xa6050743cc0f3313

def z311 : W := mkw 0x4bcc3f7c77f1ff12 0x44bcc3f7c77f1ff1 0xefcc7ff83fe0fe0d 0xfefcc7ff83fe0fe0

def z312 : W := mkw 0x200000000c0aa0a1 0x0200000000c0aa0a 0x000000003c0cc0c0 0x1000000003c0cc0c

def z313 : W := mkw 0x0f700d2280000000 0x00f700d228000000 0x8ff00fffc0000007 0xe8ff00fffc000000

def z314 : W := mkw 0x108490003bdf000c 0x0108490003bdf000 0x405c70003fff000b 0xb405c70003fff000

def z315 : W := mkw 0x0430000000000000 0x0043000000000000 0x0e30000000000002 0xe0e3000000000000

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z317 : W := mkw 0x5ff2cd683eaefc0e 0x05ff2cd683eaefc0 0xffe38ff83fecfe0d 0xfffe38ff83fecfe0

def z318 : W := mkw 0x8f7b6fb7c80a0000 0x08f7b6fb7c80a000 0xdffffffffc1f000f 0xfdffffffffc1f000

def z319 : W := mkw 0x0004100801711712 0x4000410080171171 0x6000000003f33f38 0x06000000003f33f3

def z320 : W := mkw 0x0084904823755f5a 0xc0084904823755f5 0x6000000023fffff8 0x16000000023fffff

def z321 : W := mkw 0x843f7297c1510310 0x4843f7297c151031 0x103ff007c0130132 0x0103ff007c013013

def z322 : W := mkw 0x3fffdec7bfdfebed 0x83fffdec7bfdfebe 0xffffffc7ffffffff 0xfffffffc7fffffff

def z323 : W := mkw 0x008db2dd63755f5a 0xc008db2dd63755f5 0xb1effbff23fccfcf 0x7b1effbff23fccfc

def z324 : W := mkw 0x1000100018cb0004 0x01000100018cb000 0x400000001ce30000 0x0400000001ce3000

def z325 : W := mkw 0x208480402f1eebe9 0x8208480402f1eebe 0x600000003f1ffff8 0x1600000003f1ffff

def z326 : W := mkw 0x000db29d4175175a 0xc000db29d4175175 0xf07ff63fc3ff3fff 0xaf07ff63fc3ff3ff

def z327 : W := mkw 0x1dffd2853bdf034c 0x81dffd2853bdf034 0x5ffff0073fff01cb 0xf5ffff0073fff01c

def z328 : W := mkw 0x263c3e1ecd7bb7b3 0x4263c3e1ecd7bb7b 0xee5c763cdff33f3f 0xaee5c763cdff33f3

def z329 : W := mkw 0x000d828501140348 0x8000d82850114034 0x302f8807201cc1ce 0x7302f8807201cc1c

def z330 : W := mkw 0x0004100801711712 0x4000410080171171 0xe040063803f33f3d 0xae040063803f33f3

def z331 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fa38fffc0000004 0x49fa38fffc000000

def z332 : W := mkw 0x8433408380000000 0x0843340838000000 0x1023800300000000 0x0102380030000000

def z333 : W := mkw 0x1d7e721c59fb1716 0x41d7e721c59fb171 0xee5c763cdff33f3f 0xaee5c763cdff33f3

def z334 : W := mkw 0xcf726d3ad4a0b402 0x0cf726d3ad4a0b40 0x4e507438dce03000 0x84e507438dce0300

def z335 : W := mkw 0x26303c1acc6bb4b3 0x426303c1acc6bb4b 0x6e707c3ffcfff1fe 0xf6e707c3ffcfff1f

def z336 : W := mkw 0x22000c028400a0a1 0x022000c028400a0a 0x60100c07c013f1fe 0xa60100c07c013f1f

def z337 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefd00ffcfff3ff3f 0xfefd00ffcfff3ff3

def z338 : W := mkw 0x49c0016032804800 0x049c001603280480 0x018001c000000000 0x0018001c00000000

def z339 : W := mkw 0x26341c0a8d7bb7b3 0x426341c0a8d7bb7b 0x6e300c07fffffffe 0xf6e300c07fffffff

def z340 : W := mkw 0x008da2d563144b48 0x8008da2d563144b4 0xb1ffffffe31ccfcf 0xfb1ffffffe31ccfc

def z341 : W := mkw 0x42000d280420b402 0x042000d280420b40 0x0000043800003000 0x0000004380000300

def z342 : W := mkw 0x008cb25c63755f5a 0xc008cb25c63755f5 0xe05c763ce3ffffff 0xbe05c763ce3fffff

def z343 : W := mkw 0x2f724c028c0aa0a1 0x02f724c028c0aa0a 0x7ffffc07fc1ff1ff 0xf7ffffc07fc1ff1f

def z344 : W := mkw 0x06300c0280000000 0x006300c028000000 0x0e20080300000000 0x40e2008030000000

def z345 : W := mkw 0x42800d682620fc02 0x042800d682620fc0 0xa1800ff82300fe0d 0x7a1800ff82300fe0

def z346 : W := mkw 0x243c321ec97b17b3 0x4243c321ec97b17b 0xe07c763fc3ff3fff 0xae07c763fc3ff3ff

def z347 : W := mkw 0x4bcc0f6c37b0ff02 0x04bcc0f6c37b0ff0 0xefcc0ffc3ff0ff0f 0xfefcc0ffc3ff0ff0

def z348 : W := mkw 0x008db2dd63755f5a 0xc008db2dd63755f5 0x91cff3f803e00e01 0x091cff3f803e00e0

def z349 : W := mkw 0x59c6d16833f55c0e 0x059c6d16833f55c0 0x91cff3f803e00e01 0x091cff3f803e00e0

def z350 : W := mkw 0x6bc00d683eaafca3 0x06bc00d683eaafca 0xefc00ff83ffffffd 0xfefc00ff83ffffff

def z351 : W := mkw 0x4bc41d6837f1fc02 0x04bc41d6837f1fc0 0xefdc7ff83ff3fe0f 0xfefdc7ff83ff3fe0

def z352 : W := mkw 0x008c820423140308 0x0008c82042314030 0xb1af8204231c0f0f 0x7b1af8204231c0f0

def z353 : W := mkw 0x0d7a621440000000 0x00d7a62144000000 0x9ffff63cc0000007 0xe9ffff63cc000000

def z354 : W := mkw 0x4940012810a01402 0x04940012810a0140 0x0040003800e00000 0x00040003800e0000

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0x60300c07e01ff1fe 0xf60300c07e01ff1f

def z356 : W := mkw 0x8f7b7fbfc0611412 0x48f7b7fbfc061141 0xdfffffffc0e33037 0xedfffffffc0e3303

def z357 : W := mkw 0x000d32dd41715f52 0xc000d32dd41715f5 0xe05c7fffc3f3ffff 0xae05c7fffc3f3fff

def z358 : W := mkw 0x0004800001140348 0x8000480000114034 0x00000000001c01c0 0x000000000001c01c

def z359 : W := mkw 0x9ffffff7fbdf4b4c 0x89ffffff7fbdf4b4 0xffffffffffffcfcf 0xfffffffffffffcfc

def z360 : W := mkw 0x263c3e16cd5ba3b1 0x4263c3e16cd5ba3b 0x6e3c7c07fc1ff1fe 0xf6e3c7c07fc1ff1f

def z361 : W := mkw 0x14325000084b0004 0x014325000084b000 0x0010700000030000 0x0001070000003000

def z362 : W := mkw 0x4bcd8fed37b4ff4a 0x84bcd8fed37b4ff4 0xffcf8ff83fe0fe0d 0xfffcf8ff83fe0fe0

def z363 : W := mkw 0x020c3e1c4571b712 0x4020c3e1c4571b71 0xee5c7e3cfff3ff3f 0xfee5c7e3cfff3ff3

def z364 : W := mkw 0x26300c02880a00a1 0x026300c02880a00a 0x0e300c07c01f01f6 0xe0e300c07c01f01f

def z365 : W := mkw 0x008180c122044848 0x8008180c12204484 0x118381c000000000 0x0118381c00000000

def z366 : W := mkw 0x243c3216c95b03b1 0x4243c3216c95b03b 0x003c7007c01f01f2 0x0003c7007c01f01f

def z367 : W := mkw 0x0b482f3440000000 0x00b482f344000000 0x8fdc7ffcc0000007 0xe8fdc7ffcc000000

def z368 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e2008033c1ff1f8 0x56e2008033c1ff1f

def z369 : W := mkw 0x000d028501100300 0x0000d02850110030 0xb1af8bc703100f0f 0x6b1af8bc703100f0

def z370 : W := mkw 0x108490003bdf000c 0x0108490003bdf000 0x51af80003fff000b 0x751af80003fff000

def z371 : W := mkw 0x19cfd2c533d54b4c 0x819cfd2c533d54b4 0xb1effbc723fccfcf 0x7b1effbc723fccfc

def z372 : W := mkw 0x6ff00d62be8ae8a1 0x06ff00d62be8ae8a 0x6fb00dc7fc1ff1fe 0xf6fb00dc7fc1ff1f

def z373 : W := mkw 0x8fffefb7e3140008 0x08fffefb7e314000 0x9fffffffe31c000f 0xf9fffffffe31c000

def z374 : W := mkw 0x0940000010800000 0x0094000001080000 0x4e4000001ce00000 0x84e4000001ce0000

def z375 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xa04c723c03f00f0f 0x2a04c723c03f00f0

def z376 : W := mkw 0x000c020401100300 0x0000c02040110030 0x000c000400100102 0x0000c00040010010

def z377 : W := mkw 0x008d92cd23755f5a 0xc008d92cd23755f5 0xf1af8bc723ffffff 0x7f1af8bc723fffff

def z378 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xdfffffffdc033037 0xedfffffffdc03303

def z379 : W := mkw 0x843fe297c1140348 0x8843fe297c114034 0x103ff007c01c01c2 0x0103ff007c01c01c

def z380 : W := mkw 0x5bc6dd6837f5fc0e 0x05bc6dd6837f5fc0 0xffcffff83fe0fe0d 0xfffcffff83fe0fe0

def z381 : W := mkw 0xcbcb6ffd76a0fc02 0x0cbcb6ffd76a0fc0 0xffcffff83fe0fe0d 0xfffcffff83fe0fe0

def z382 : W := mkw 0x09c0000832a01402 0x009c0000832a0140 0xefc006383fe03e0d 0xfefc006383fe03e0

def z383 : W := mkw 0x19c2c0003284000c 0x019c2c0003284000 0x1183800000000000 0x0118380000000000

def z384 : W := mkw 0x02800c402600e800 0x002800c402600e80 0xef800fc03f00fe0d 0xfef800fc03f00fe0

def z385 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0x405c743cc0f33132 0x8405c743cc0f3313

def z386 : W := mkw 0x3f725c029ccba0a5 0x03f725c029ccba0a 0x4e507400dce33030 0x84e507400dce3303

def z387 : W := mkw 0x26300c0a8c2ab4a3 0x026300c0a8c2ab4a 0xee700e3fffffffff 0xfee700e3ffffffff

def z388 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x0e300807fc1fc1f2 0x50e300807fc1fc1f

def z389 : W := mkw 0x0080004022004800 0x0008000402200480 0x200000002300ce08 0x1200000002300ce0

def z390 : W := mkw 0x0084804023144b48 0x80084804023144b4 0xa1800bc0231ccfcd 0x7a1800bc0231ccfc

def z391 : W := mkw 0x06300c0280000000 0x006300c028000000 0x6e300c07c013313e 0xe6e300c07c013313

def z392 : W := mkw 0x000c321441510000 0x0000c32144151000 0xc05c763cc3f3000f 0xac05c763cc3f3000

def z393 : W := mkw 0x0430000280000000 0x0043000028000000 0x00300007c0000002 0x000300007c000000

def z394 : W := mkw 0x000d828501140348 0x8000d82850114034 0x91af8bc7001c01c7 0x691af8bc7001c01c

def z395 : W := mkw 0x008db2dd63755f5a 0xc008db2dd63755f5 0xf1dff7fcc3f33f3f 0xaf1dff7fcc3f33f3

def z396 : W := mkw 0x0f724d2000000000 0x00f724d200000000 0x9ffffff800000007 0xe9ffffff80000000

def z397 : W := mkw 0x943ff297c95f000c 0x0943ff297c95f000 0x103ff007c01f0002 0x0103ff007c01f000

def z398 : W := mkw 0x1df2d0003acf000c 0x01df2d0003acf000 0x5ff3f0003cef0000 0xd5ff3f0003cef000

def z399 : W := mkw 0x8f7a6f36c0000000 0x08f7a6f36c000000 0x8e5c763cc0000007 0xa8e5c763cc000000

def z400 : W := mkw 0x000c321441510310 0x4000c32144151031 0x000c700000000000 0x0000c70000000000

def z401 : W := mkw 0x19cfd2c533d54b4c 0x819cfd2c533d54b4 0x91cff3c003e00e01 0x091cff3c003e00e0

def z402 : W := mkw 0x000100c100004840 0x8000100c10000484 0x000009c30000c0c0 0x0000009c30000c0c

def z403 : W := mkw 0x1dffc2c53b9e4b4c 0x81dffc2c53b9e4b4 0xbfaf8bc73f1ccfcf 0x7bfaf8bc73f1ccfc

def z404 : W := mkw 0x04341000095b0000 0x004341000095b000 0x4e7c70003fff000b 0xf4e7c70003fff000

def z405 : W := mkw 0x408000403680e800 0x0408000403680e80 0x000000003c00c000 0x1000000003c00c00

def z406 : W := mkw 0x84326012c0000000 0x084326012c000000 0x00107000c0000000 0x000107000c000000

def z407 : W := mkw 0x00000000080a0000 0x000000000080a000 0x400000003c1f0008 0x1400000003c1f000

def z408 : W := mkw 0x2ff00c02be8aa0a1 0x02ff00c02be8aa0a 0x6ff00c07fffff1ff 0xf6ff00c07fffff1f

def z409 : W := mkw 0xbfffffb7ffdfa0ad 0x0bfffffb7ffdfa0a 0xfffffffffffff1ff 0xffffffffffffff1f

def z410 : W := mkw 0x0df2400032800000 0x00df240003280000 0x5ffff0003fe0000b 0xf5ffff0003fe0000

def z411 : W := mkw 0x0008221440000310 0x4000822144000031 0x00000004c0000130 0x000000004c000013

def z412 : W := mkw 0x1df6d0083bff171e 0x41df6d0083bff171 0x7ffff0003fff3f3b 0xf7ffff0003fff3f3

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000201cc1c8 0x120000000201cc1c

def z414 : W := mkw 0x26300c028400a0a1 0x026300c028400a0a 0x2e300c07c000f1f6 0xe2e300c07c000f1f

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x005c700000000003 0xa005c70000000000

def z416 : W := mkw 0x1df2c0003a8e000c 0x01df2c0003a8e000 0x5fe380003fec0009 0xf5fe380003fec000

def z417 : W := mkw 0x0080804022044848 0x8008080402204484 0x00000000200cc0c0 0x100000000200cc0c

def z418 : W := mkw 0x26382e16cc0aa0a1 0x026382e16cc0aa0a 0xee7c7e3ffc1ff1ff 0xfee7c7e3ffc1ff1f

def z419 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e300400fc1f303a 0xf4e300400fc1f303

def z420 : W := mkw 0x0d72400000000000 0x00d7240000000000 0x0e50700000000000 0x80e5070000000000

def z421 : W := mkw 0xa6392fb7cc0aa0a1 0x0a6392fb7cc0aa0a 0xee300ffffc1ff1fe 0xfee300ffffc1ff1f

def z422 : W := mkw 0x843b6297c0000000 0x0843b6297c000000 0x103ff007c0000002 0x0103ff007c000000

def z423 : W := mkw 0x263c0e068d1aa3a1 0x0263c0e068d1aa3a 0xee3c0e07ff1fffff 0xfee3c0e07ff1ffff

def z424 : W := mkw 0x1d72701858eb1416 0x41d72701858eb141 0x4e507438dce33030 0x84e507438dce3303

def z425 : W := mkw 0x1df2c0003a8e000c 0x01df2c0003a8e000 0x1ffff0003c0c0003 0xf1ffff0003c0c000

def z426 : W := mkw 0x09c4800033940008 0x009c480003394000 0x5fef80003ffc000b 0xf5fef80003ffc000

def z427 : W := mkw 0x24300002880a00a1 0x024300002880a00a 0x20300807e01fc1fe 0x720300807e01fc1f

def z428 : W := mkw 0x84bfe2d7e3144b48 0x884bfe2d7e3144b4 0xb1bffbc7e31ccfcf 0x7b1bffbc7e31ccfc

def z429 : W := mkw 0x200000000c0aa0a1 0x0200000000c0aa0a 0x60100404fc1ff1fe 0xb60100404fc1ff1f

def z430 : W := mkw 0x0004800001140008 0x0000480000114000 0x102f8000001c0002 0x0102f8000001c000

def z431 : W := mkw 0x0009028500000000 0x0000902850000000 0xb1af8bc7201cc1cf 0x7b1af8bc7201cc1c

def z432 : W := mkw 0x04300000080a0000 0x004300000080a000 0x0e2000003c0c0000 0x50e2000003c0c000

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200000201c000a 0x700200000201c000

def z434 : W := mkw 0x9ff3cda3ba8e000c 0x09ff3cda3ba8e000 0x1fa389c33c0c0000 0x51fa389c33c0c000

def z435 : W := mkw 0x008902c522004800 0x0008902c52200480 0xb1af8bc72300ce0f 0x7b1af8bc72300ce0

def z436 : W := mkw 0x243d8287891e03e9 0x8243d8287891e03e 0x103f8007c01f01f2 0x0103f8007c01f01f

def z437 : W := mkw 0x008c325c63715f12 0x4008c325c63715f1 0xe1dc7ffce3f3ff3f 0xfe1dc7ffce3f3ff3

def z438 : W := mkw 0x26b18cc3ae0ee8e9 0x826b18cc3ae0ee8e 0x1fa389c33c0cc0c0 0x51fa389c33c0cc0c

def z439 : W := mkw 0x86392fb7c0000000 0x086392fb7c000000 0x8e300fffc0000006 0xe8e300fffc000000

def z440 : W := mkw 0x9f727d32d8cb0004 0x09f727d32d8cb000 0x4e507438dce30000 0x84e507438dce3000

def z441 : W := mkw 0x9ff7dda3bbdf000c 0x09ff7dda3bbdf000 0x5ffff9c33fff000b 0xf5ffff9c33fff000

def z442 : W := mkw 0x008da2dd63345f5a 0xc008da2dd63345f5 0xb1af8fffe31cffff 0x7b1af8fffe31cfff

def z443 : W := mkw 0x8f734da380000000 0x08f734da38000000 0x1ffff9c300000003 0xe1ffff9c30000000

def z444 : W := mkw 0x0b400d200400a000 0x00b400d200400a00 0xefc00ff83c00f00d 0xfefc00ff83c00f00

def z445 : W := mkw 0x26bdbedfef7ffffb 0xc26bdbedfef7ffff 0xffffffffffffffff 0xffffffffffffffff

def z446 : W := mkw 0x0432400000000000 0x0043240000000000 0x103ff00000000002 0x0103ff0000000000

def z447 : W := mkw 0x0004100001510000 0x0000410000151000 0x4000000003f30008 0x04000000003f3000

def z448 : W := mkw 0x0080004022004800 0x0008000402200480 0x818003c003000e01 0x0818003c003000e0

def z449 : W := mkw 0x008982c522044848 0x8008982c52204484 0x91af8bc7200cc0c7 0x791af8bc7200cc0c

def z450 : W := mkw 0x4bc00d2836a0b402 0x04bc00d2836a0b40 0x4fc004383fe03009 0xf4fc004383fe0300

def z451 : W := mkw 0x9f7b7fb7d8cb0004 0x09f7b7fb7d8cb000 0xdfffffffdce30007 0xedfffffffdce3000

def z452 : W := mkw 0xcf7b6fffc420fc02 0x0cf7b6fffc420fc0 0xbfffffffc000fe07 0xebfffffffc000fe0

def z453 : W := mkw 0x9fffffbffbff171e 0x49fffffbffbff171 0xffffffffffff3f3f 0xfffffffffffff3f3

def z454 : W := mkw 0x42000d680420fc02 0x042000d680420fc0 0xe0400ff803e0fe0d 0xae0400ff803e0fe0

def z455 : W := mkw 0x4080004836a0fc02 0x04080004836a0fc0 0xe1800bc03fe0fe0d 0x7e1800bc03fe0fe0

def z456 : W := mkw 0x26341c028d5ba0a1 0x026341c028d5ba0a 0x6e7c7c07fffff1ff 0xf6e7c7c07fffff1f

def z457 : W := mkw 0x0009028500000340 0x8000902850000034 0x00000007000001c0 0x000000007000001c

def z458 : W := mkw 0x49cd83ed33b45f4a 0x849cd83ed33b45f4 0x91cf83f803e00e01 0x091cf83f803e00e0

def z459 : W := mkw 0x06300c000c0aa000 0x006300c000c0aa00 0x6e300c003c1ff00e 0xf6e300c003c1ff00

def z460 : W := mkw 0x820d3fbfc1711712 0x4820d3fbfc171171 0xe05c7fffc3f33f3f 0xae05c7fffc3f33f3

def z461 : W := mkw 0x008580c123144b48 0x8008580c123144b4 0x31a389c3231ccfc8 0x531a389c3231ccfc

def z462 : W := mkw 0x04300000080a0000 0x004300000080a000 0x6e300404fc1f313e 0xf6e300404fc1f313

def z463 : W := mkw 0x0008221440000000 0x0000822144000000 0xe05c763cc013313f 0xae05c763cc013313

def z464 : W := mkw 0x0d72400000000000 0x00d7240000000000 0x1fa3800000000000 0x41fa380000000000

def z465 : W := mkw 0x4084804837b4ff4a 0x84084804837b4ff4 0x600000003ffcffc8 0x1600000003ffcffc

def z466 : W := mkw 0x19c6d0003bdf000c 0x019c6d0003bdf000 0x51cff0003fff0009 0x151cff0003fff000

def z467 : W := mkw 0x208d82c52f1eebe9 0x8208d82c52f1eebe 0xf1af8bc73f1fffff 0x7f1af8bc73f1ffff

def z468 : W := mkw 0x000d828501140348 0x8000d82850114034 0xb02f8207031c0fcf 0x2b02f8207031c0fc

def z469 : W := mkw 0x04bd82c52b1e4b48 0x804bd82c52b1e4b4 0xffbf8bc73f1fcfcf 0xfffbf8bc73f1fcfc

def z470 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe000063cc3f33f3c 0x0e000063cc3f33f3

def z471 : W := mkw 0x82092fb7c0000000 0x082092fb7c000000 0x805c7fffc0000007 0xa805c7fffc000000

def z472 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x1e7ff43fc0000002 0x81e7ff43fc000000

def z473 : W := mkw 0x0004100801711402 0x0000410080171140 0xe05c763803f33e0f 0xae05c763803f33e0

def z474 : W := mkw 0x0084804023144b48 0x80084804023144b4 0x31af8000231ccfcb 0x731af8000231ccfc

def z475 : W := mkw 0x4bc18de936a4fc4a 0x84bc18de936a4fc4 0xffe38ffb3fecfecd 0xfffe38ffb3fecfec

def z476 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xf1bf8fc7e31fffff 0xff1bf8fc7e31ffff

def z477 : W := mkw 0x6f700d2a9caab4a3 0x06f700d2a9caab4a 0x4e500438dce33030 0x84e500438dce3303

def z478 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xaf800ff83c00fe04 0x5af800ff83c00fe0

def z479 : W := mkw 0x66b00c4abeaafca3 0x066b00c4abeaafca 0x6e300c07fffffffe 0xf6e300c07fffffff

def z480 : W := mkw 0x1dfef2147bdf031c 0x41dfef2147bdf031 0x5ffff004ffff013b 0xf5ffff004ffff013

def z481 : W := mkw 0x0b400d2000000000 0x00b400d200000000 0x0f8009c000000000 0x40f8009c00000000

def z482 : W := mkw 0x0d7b428500000000 0x00d7b42850000000 0x9ffffbc700000007 0xe9ffffbc70000000

def z483 : W := mkw 0x200000000c0aa0a1 0x0200000000c0aa0a 0x400000001c033030 0x0400000001c03303

def z484 : W := mkw 0x0004100001510000 0x0000410000151000 0x605c7404c3f3313f 0xa605c7404c3f3313

def z485 : W := mkw 0xeffb6ffffeaafca3 0x0effb6ffffeaafca 0xffffffffffffffff 0xffffffffffffffff

def z486 : W := mkw 0x8f7f6fb7c1100300 0x08f7f6fb7c110030 0xbfffffffc3100f0f 0xebfffffffc3100f0

def z487 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0x6f8009c03fe0fe08 0x56f8009c03fe0fe0

def z488 : W := mkw 0x008c824423144b48 0x8008c824423144b4 0xa00c0204231ccfcf 0x3a00c0204231ccfc

def z489 : W := mkw 0x6ffd8fefbfbeffeb 0x86ffd8fefbfbeffe 0xffff8fffffffffff 0xfffff8ffffffffff

def z490 : W := mkw 0x5ff6dd283fffb40e 0x05ff6dd283fffb40 0x5ffff4383fff300b 0xf5ffff4383fff300

def z491 : W := mkw 0x24300002880a00a1 0x024300002880a00a 0x4e300007fc1f01fa 0xf4e300007fc1f01f

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000020003000e0d 0x2a000020003000e0

def z493 : W := mkw 0x0080004022004800 0x0008000402200480 0x018009c02000c000 0x5018009c02000c00

def z494 : W := mkw 0x3ffefe1effffb7bf 0x43ffefe1effffb7b 0xfffffe3fffffffff 0xffffffe3ffffffff

def z495 : W := mkw 0x82002d32c0000000 0x082002d32c000000 0x00000438c0000000 0x000000438c000000

def z496 : W := mkw 0x8f726d32c0000000 0x08f726d32c000000 0x8fd07ff8c0000005 0xe8fd07ff8c000000

def z497 : W := mkw 0xcffb6ffff2a05c02 0x0cffb6ffff2a05c0 0x9fffffffc3e00e07 0xe9fffffffc3e00e0

def z498 : W := mkw 0xaf734da38c0aa0a1 0x0af734da38c0aa0a 0x1fa389c33c0cc0c0 0x51fa389c33c0cc0c

def z499 : W := mkw 0x4bc00d603680e800 0x04bc00d603680e80 0x8fc00ff83c00c005 0xf8fc00ff83c00c00

def z500 : W := mkw 0x1df250003acb0004 0x01df250003acb000 0x4fd070003fe30009 0xf4fd070003fe3000

def z501 : W := mkw 0x1df6d0403bdf4b4c 0x81df6d0403bdf4b4 0x7ffff0003fffcfcb 0xf7ffff0003fffcfc

def z502 : W := mkw 0x3ff6dc02bfdfa0ad 0x03ff6dc02bfdfa0a 0x5ffff8033fffc0cb 0xf5ffff8033fffc0c

def z503 : W := mkw 0x0001808100040048 0x8000180810004004 0x10238003000c00c0 0x010238003000c00c

def z504 : W := mkw 0x09c4100033d10000 0x009c4100033d1000 0x4fdc70003ff3000b 0xf4fdc70003ff3000

def z505 : W := mkw 0x7ff6dd6abffffcaf 0x07ff6dd6abffffca 0xffffffffffffffff 0xffffffffffffffff

def z506 : W := mkw 0x0008221c40201712 0x40008221c4020171 0xe010063cc0133f3e 0xae010063cc0133f3

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x40100400c0033030 0x840100400c003303

def z508 : W := mkw 0x000d02c501104b40 0x8000d02c501104b4 0xa00c0bc70310cfcf 0x2a00c0bc70310cfc

def z509 : W := mkw 0x26303c1acc6bb4b3 0x426303c1acc6bb4b 0x4e507438dce33030 0x84e507438dce3303

def z510 : W := mkw 0x4bc00d603680e800 0x04bc00d603680e80 0x4fc009c03fe0c009 0xf4fc009c03fe0c00

def z511 : W := mkw 0x1d72500018cb0004 0x01d72500018cb000 0x4e7070003cff000a 0xf4e7070003cff000

def z512 : W := mkw 0x89cfe3f563144b48 0x889cfe3f563144b4 0x91cff3f803000e01 0x091cff3f803000e0

def z513 : W := mkw 0x828daff7e3144b48 0x8828daff7e3144b4 0xb1af8fffe31ccfcf 0x7b1af8fffe31ccfc

def z514 : W := mkw 0x843b6297c0000000 0x0843b6297c000000 0x91bffbc7c0000007 0x691bffbc7c000000

def z515 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e200c033c0cf0cc 0xf6e200c033c0cf0c

def z516 : W := mkw 0x6ff00d6abeaafca3 0x06ff00d6abeaafca 0xefd00ff8ffe3fe3d 0xfefd00ff8ffe3fe3

def z517 : W := mkw 0x26b18cc3ae0ee8e9 0x826b18cc3ae0ee8e 0x7fb38dc7fc1ff1fe 0xf7fb38dc7fc1ff1f

def z518 : W := mkw 0x1ff6dd203bdf000c 0x01ff6dd203bdf000 0xdffffff83fff000f 0xfdffffff83fff000

def z519 : W := mkw 0x108080003a8e000c 0x0108080003a8e000 0x000000003c0c0000 0x1000000003c0c000

def z520 : W := mkw 0x04300000080a0000 0x004300000080a000 0x00300000001f0002 0x000300000001f000

def z521 : W := mkw 0x09c0000032800000 0x009c000003280000 0x0f8000003c000000 0x50f8000003c00000

def z522 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x20000c000000f004 0x020000c000000f00

def z523 : W := mkw 0x8b492fb7c0000000 0x08b492fb7c000000 0x8fc00fffc0000005 0xe8fc00fffc000000

def z524 : W := mkw 0x028d8ec52714eb48 0x8028d8ec52714eb4 0xffaf8fc73f1cffcf 0xfffaf8fc73f1cffc

def z525 : W := mkw 0xcff34de3b680e800 0x0cff34de3b680e80 0x1fa389c33c00c000 0x51fa389c33c00c00

def z526 : W := mkw 0x1df7d0c13bdf484c 0x81df7d0c13bdf484 0x5ffff9c33fffc0cb 0xf5ffff9c33fffc0c

def z527 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x0e300c07fc0cc0c6 0xf0e300c07fc0cc0c

def z528 : W := mkw 0x0084800023140008 0x0008480002314000 0x31af8807231cc1cf 0x731af8807231cc1c

def z529 : W := mkw 0xaf7f7fbfcd7bb7b3 0x4af7f7fbfcd7bb7b 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x1fbff0003c1f0002 0x51fbff0003c1f000

def z531 : W := mkw 0x09c0004032804800 0x009c000403280480 0xefc00bc03fe0ce0d 0xfefc00bc03fe0ce0

def z532 : W := mkw 0x0000000000000000 0x0000000000000000 0x81800bc000000005 0x681800bc00000000

def z533 : W := mkw 0x5ff2cd603e8ee80c 0x05ff2cd603e8ee80 0x1fa389c03c0cc000 0x51fa389c03c0cc00

def z534 : W := mkw 0x06bd8ec7a3144b48 0x806bd8ec7a3144b4 0xbfbf8fc7e31ccfcf 0xfbfbf8fc7e31ccfc

def z535 : W := mkw 0x0084804023144b48 0x80084804023144b4 0x20200807231ccfce 0x720200807231ccfc

def z536 : W := mkw 0x8f7f7fbfc1711712 0x48f7f7fbfc171171 0x9fffffffc3e00e07 0xe9fffffffc3e00e0

def z537 : W := mkw 0x0008221440000000 0x0000822144000000 0x001c7004c0000002 0x0001c7004c000000

def z538 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xcfc007f81fe03e01 0x8cfc007f81fe03e0

def z539 : W := mkw 0x22000c028400a0a1 0x022000c028400a0a 0x6e000c07fc00f1fc 0xf6e000c07fc00f1f

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x600004000000300c 0xa600004000000300

def z541 : W := mkw 0x8f7f7fb7c1510310 0x48f7f7fb7c151031 0x9fffffffc0130137 0xe9fffffffc013013

def z542 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5fdff0001fe30001 0x85fdff0001fe3000

def z543 : W := mkw 0x19cef21c73f5171e 0x419cef21c73f5171 0xf1dff63cc3f33f3f 0xaf1dff63cc3f33f3

def z544 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e300c03fc0ff0f0 0xd4e300c03fc0ff0f

def z545 : W := mkw 0xcfff7ffff7f1ff12 0x4cfff7ffff7f1ff1 0xfffffffffff3ff3f 0xffffffffffff3ff3

def z546 : W := mkw 0x1df3c0c13a8e484c 0x81df3c0c13a8e484 0x1fa389c33c0cc0c0 0x51fa389c33c0cc0c

def z547 : W := mkw 0x008d828523140348 0x8008d82852314034 0x11af8007231c01cb 0x711af8007231c01c

def z548 : W := mkw 0x308490003fdfa0ad 0x0308490003fdfa0a 0x600000003ffff1f8 0x1600000003ffff1f

def z549 : W := mkw 0x220c3e1ec571b7b3 0x4220c3e1ec571b7b 0xe05c7e3fc3f3ffff 0xae05c7e3fc3f3fff

def z550 : W := mkw 0xa63b6e97cc0aa0a1 0x0a63b6e97cc0aa0a 0x7e3ffc07fc1ff1fe 0xf7e3ffc07fc1ff1f

def z551 : W := mkw 0x8f736db3c0000000 0x08f736db3c000000 0x1ff3fdfbc0000000 0xc1ff3fdfbc000000

def z552 : W := mkw 0x000c020401100300 0x0000c02040110030 0x800c020003000e01 0x0800c020003000e0

def z553 : W := mkw 0x02000c080420b402 0x002000c080420b40 0xee400e383fe0fe0d 0xfee400e383fe0fe0

def z554 : W := mkw 0x008c024423104b00 0x0008c024423104b0 0xa18c0bc42310cf0f 0x7a18c0bc42310cf0

def z555 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x6e100c04fc13f13e 0xf6e100c04fc13f13

def z556 : W := mkw 0x0b490fa500000000 0x00b490fa50000000 0x9fef8fff00000007 0xe9fef8fff0000000

def z557 : W := mkw 0x0004301841711412 0x4000430184171141 0x405c7438c3f3303b 0xa405c7438c3f3303

def z558 : W := mkw 0x000902c500004b40 0x8000902c500004b4 0x800003c000000e00 0x0800003c000000e0

def z559 : W := mkw 0x06300c02880a0000 0x006300c02880a000 0x4e300c07fc1f000e 0xf4e300c07fc1f000

def z560 : W := mkw 0x408d82cd37b4ff4a 0x8408d82cd37b4ff4 0xf1af8bc73ffcffcf 0x7f1af8bc73ffcffc

def z561 : W := mkw 0x1dfed2043bdf030c 0x01dfed2043bdf030 0xfffff2043fff0f0f 0xffffff2043fff0f0

def z562 : W := mkw 0x4bc48d6837b4fc0a 0x04bc48d6837b4fc0 0xffef8ff83ffcfe0f 0xfffef8ff83ffcfe0

def z563 : W := mkw 0x000c221441100300 0x0000c22144110030 0xa05c763cc3100f0f 0xaa05c763cc3100f0

def z564 : W := mkw 0x1436d000095f000c 0x01436d000095f000 0x5e3ff0003c1f000a 0xf5e3ff0003c1f000

def z565 : W := mkw 0x000d828501140348 0x8000d82850114034 0x100f800000000000 0x0100f80000000000

def z566 : W := mkw 0x42082f7c4420ff12 0x442082f7c4420ff1 0xa0000ffcc000ff34 0x0a0000ffcc000ff3

def z567 : W := mkw 0x4b400d6814a0fc02 0x04b400d6814a0fc0 0xee400ff81ce0fe04 0x8ee400ff81ce0fe0

def z568 : W := mkw 0x5bc49d683ffffc0e 0x05bc49d683ffffc0 0xefc00ff83ffffe0d 0xfefc00ff83ffffe0

def z569 : W := mkw 0x62000d6a8420fca3 0x062000d6a8420fca 0xa0000fffc000fff4 0x0a0000fffc000fff

def z570 : W := mkw 0x42000d600400e800 0x042000d600400e80 0x000009c00000c000 0x0000009c00000c00

def z571 : W := mkw 0x0009028500000000 0x0000902850000000 0x80000bc700000004 0x080000bc70000000

def z572 : W := mkw 0x000c221c41301712 0x4000c221c4130171 0xa00c063cc3103f3f 0x2a00c063cc3103f3

def z573 : W := mkw 0x8fffeff7e3144b48 0x88fffeff7e3144b4 0x9fffffffc3000e07 0xe9fffffffc3000e0

def z574 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe04c723803f33f39 0x0e04c723803f33f3

def z575 : W := mkw 0x2f700d228c0aa0a1 0x02f700d228c0aa0a 0xeff00ffffc1ff1ff 0xfeff00ffffc1ff1f

def z576 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x0e0000001c000000 0x00e0000001c00000

def z577 : W := mkw 0x000c020c01301702 0x0000c020c0130170 0xe04c063c03f03f0f 0xae04c063c03f03f0

def z578 : W := mkw 0x420c3f7c4571ff12 0x4420c3f7c4571ff1 0xe05c7ffcc3f3ff3f 0xae05c7ffcc3f3ff3

def z579 : W := mkw 0x82092fb7c0000000 0x082092fb7c000000 0x91af8fffc0000007 0x691af8fffc000000

def z580 : W := mkw 0xa2092fb7c400a0a1 0x0a2092fb7c400a0a 0xa0000fffc000f1f4 0x0a0000fffc000f1f

def z581 : W := mkw 0x8f734da380000000 0x08f734da38000000 0x1fb38dc7c0000006 0xe1fb38dc7c000000

def z582 : W := mkw 0x42090fed0420ff42 0x842090fed0420ff4 0xa0000fff0000ffc4 0x0a0000fff0000ffc

def z583 : W := mkw 0x000c020401100300 0x0000c02040110030 0xa02c0a07231ccfcf 0x7a02c0a07231ccfc

def z584 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000001 0xe0fc000000000000

def z585 : W := mkw 0x6ffc3f7efffbffb3 0x46ffc3f7efffbffb 0xeffc7fffffffffff 0xfeffc7ffffffffff

def z586 : W := mkw 0x1dffd2853bdf000c 0x01dffd2853bdf000 0xdffffbc73fff000f 0xfdffffbc73fff000

def z587 : W := mkw 0x000902c500004b40 0x8000902c500004b4 0xa0200bc7201ccfce 0x7a0200bc7201ccfc

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040063800000005 0xa804006380000000

def z589 : W := mkw 0x8f734da380000000 0x08f734da38000000 0x9fe38ffb00000005 0xe9fe38ffb0000000

def z590 : W := mkw 0x243000000c0aa0a1 0x0243000000c0aa0a 0x6e3000003c1ff1fa 0xf6e3000003c1ff1f

def z591 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb18f8bc02300ce0d 0x7b18f8bc02300ce0

def z592 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x11eff00023fc000b 0x711eff00023fc000

def z593 : W := mkw 0x200410080d7bb7b3 0x4200410080d7bb7b 0x600000003ffffff8 0x1600000003ffffff

def z594 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe04c763803e03e0d 0xae04c763803e03e0

def z595 : W := mkw 0x4ff00d6ab6a0fc02 0x04ff00d6ab6a0fc0 0xeff00fffffe0fe0f 0xfeff00fffffe0fe0

def z596 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af83c0231c0e0b 0x791af83c0231c0e0

def z597 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e300407dc1f31f2 0x84e300407dc1f31f

def z598 : W := mkw 0x0008221c40201712 0x40008221c4020171 0xe040063cc3e03f3d 0xae040063cc3e03f3

def z599 : W := mkw 0x6ff00d6abeaafca3 0x06ff00d6abeaafca 0xefe00ffb3fecfecd 0xfefe00ffb3fecfec

def z600 : W := mkw 0x894f73bd41711712 0x4894f73bd4171171 0x91cff3f803e00e01 0x091cff3f803e00e0

def z601 : W := mkw 0x22000c000c0aa0a1 0x022000c000c0aa0a 0x6e000c003c1ff1fc 0xf6e000c003c1ff1f

def z602 : W := mkw 0x0004000001100300 0x0000400000110030 0x2000000003100f08 0x02000000003100f0

def z603 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb18f83c403100f0f 0x2b18f83c403100f0

def z604 : W := mkw 0x143ef21c497f171e 0x4143ef21c497f171 0xf07ff63cc3ff3f3f 0xaf07ff63cc3ff3f3

def z605 : W := mkw 0x200c321c4d7bb7b3 0x4200c321c4d7bb7b 0xe05c763cffffffff 0xbe05c763cfffffff

def z606 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e100c00fc03f03c 0xf6e100c00fc03f03

def z607 : W := mkw 0x000c321441510310 0x4000c32144151031 0xa01c7204c3130f3f 0x2a01c7204c3130f3

def z608 : W := mkw 0x4000000814a0b402 0x04000000814a0b40 0x400000001ce03000 0x0400000001ce0300

def z609 : W := mkw 0x8ffb6fb7f2800000 0x08ffb6fb7f280000 0xdfffffffffe0000f 0xfdfffffffffe0000

def z610 : W := mkw 0x863b6e97c0000000 0x0863b6e97c000000 0x1e3ffc07c0000006 0xe1e3ffc07c000000

def z611 : W := mkw 0x0d7e721c41711712 0x40d7e721c4171171 0xfffff63cc3f33f3f 0xefffff63cc3f33f3

def z612 : W := mkw 0x108d92c53bdf4b4c 0x8108d92c53bdf4b4 0xf1af8bc73fffcfcf 0x7f1af8bc73fffcfc

def z613 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af8bc703000e07 0x691af8bc703000e0

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x11af800000000003 0x611af80000000000

def z615 : W := mkw 0x000c120401510300 0x0000c12040151030 0xe05c720403f30f0f 0xae05c720403f30f0

def z616 : W := mkw 0x26b48c42af1eebe9 0x826b48c42af1eebe 0x6e300c07ff1ffffe 0xf6e300c07ff1ffff

def z617 : W := mkw 0x0000000800201402 0x0000000080020140 0xa000063800003e04 0x0a000063800003e0

def z618 : W := mkw 0x02000d2000000000 0x002000d200000000 0x80000ff800000004 0x080000ff80000000

def z619 : W := mkw 0x0df000003a8a0000 0x00df000003a8a000 0x4ff000003fff000b 0xf4ff000003fff000

def z620 : W := mkw 0x04300000080a0000 0x004300000080a000 0x6e3008073c1fc1ce 0xf6e3008073c1fc1c

def z621 : W := mkw 0x0b4c3f3c41711712 0x40b4c3f3c4171171 0xefdc7ffcc3f33f3f 0xeefdc7ffcc3f33f3

def z622 : W := mkw 0x4bc41d6837f1ff12 0x44bc41d6837f1ff1 0xefc00ff83ff3ff3d 0xfefc00ff83ff3ff3

def z623 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x4e5070003fff0008 0x94e5070003fff000

def z624 : W := mkw 0x42800d6836a0fc02 0x042800d6836a0fc0 0xe0000ff83fe0fe0c 0x1e0000ff83fe0fe0

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000404c0003134 0x020000404c000313

def z626 : W := mkw 0x000c120c01711712 0x4000c120c0171171 0xe00c020403f33f3f 0x2e00c020403f33f3

def z627 : W := mkw 0x0bc00c003680a000 0x00bc00c003680a00 0x6fc00c003fe0f00d 0xf6fc00c003fe0f00

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x401000000013000a 0xa401000000013000

def z629 : W := mkw 0x8f7f7fb7c1510000 0x08f7f7fb7c151000 0xdfffffffc3f3000f 0xedfffffffc3f3000

def z630 : W := mkw 0x228d8ec7a714ebe9 0x8228d8ec7a714ebe 0xb1af8fc7e31cffff 0x7b1af8fc7e31cfff

def z631 : W := mkw 0x0bc00d6022004800 0x00bc00d602200480 0xafc00ff82300ce0d 0xfafc00ff82300ce0

def z632 : W := mkw 0x1d76500019db0004 0x01d76500019db000 0x4e5c70001ff3000b 0xa4e5c70001ff3000

def z633 : W := mkw 0x3ff2cc02be8ea0ad 0x03ff2cc02be8ea0a 0x1fa388033c0cc0c0 0x51fa388033c0cc0c

def z634 : W := mkw 0x000db29541550358 0xc000db2954155035 0x103ff007c01f01f2 0x0103ff007c01f01f

def z635 : W := mkw 0x22082e1ec420b7b3 0x422082e1ec420b7b 0xa0000e3fc000fff4 0x0a0000e3fc000fff

def z636 : W := mkw 0x0080004822205c02 0x00080004822205c0 0xe1c00ff823e0fe0d 0xfe1c00ff823e0fe0

def z637 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e3008033c1fc0ca 0xf4e3008033c1fc0c

def z638 : W := mkw 0x22000c028400a0a1 0x022000c028400a0a 0x00000400c0003030 0x000000400c000303

def z639 : W := mkw 0x243000028c0aa0a1 0x0243000028c0aa0a 0x60300007fc1ff1fa 0x160300007fc1ff1f

def z640 : W := mkw 0x14bfd2c52b5f4b4c 0x814bfd2c52b5f4b4 0xb1bffbc7231fcfcf 0x7b1bffbc7231fcfc

def z641 : W := mkw 0x09cd82c533944b48 0x809cd82c533944b4 0xffef8bc73ffccfcf 0xfffef8bc73ffccfc

def z642 : W := mkw 0x008d828523140008 0x0008d82852314000 0x91af8bc7231c000f 0x791af8bc7231c000

def z643 : W := mkw 0x8ffbeff7e2044848 0x88ffbeff7e204484 0x9fffffffe00cc0c7 0xf9fffffffe00cc0c

def z644 : W := mkw 0x0b400d2000000000 0x00b400d200000000 0x0e40043800000000 0x80e4004380000000

def z645 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb18f83c0231ccfc9 0x1b18f83c0231ccfc

def z646 : W := mkw 0x9ff6fd32fbdf000c 0x09ff6fd32fbdf000 0x5ffff438ffff000b 0xf5ffff438ffff000

def z647 : W := mkw 0x108cb21c7bff171e 0x4108cb21c7bff171 0xe05c763cffff3f3f 0xbe05c763cffff3f3

def z648 : W := mkw 0x000c321441510310 0x4000c32144151031 0x601c7404c013313e 0xa601c7404c013313

def z649 : W := mkw 0x14b6d0003bdf000c 0x014b6d0003bdf000 0x503ff0003fff000a 0x1503ff0003fff000

def z650 : W := mkw 0x19cef21c73f5171e 0x419cef21c73f5171 0x91cff23803e00e01 0x091cff23803e00e0

def z651 : W := mkw 0x82010da380000000 0x082010da38000000 0x000009c300000000 0x0000009c30000000

def z652 : W := mkw 0x4bc82f7c76a0fc02 0x04bc82f7c76a0fc0 0xefdc7ffcffe0fe0f 0xfefdc7ffcffe0fe0

def z653 : W := mkw 0x143fd285095f034c 0x8143fd285095f034 0x103ff007001f01c2 0x0103ff007001f01c

def z654 : W := mkw 0x4bc18de13684e848 0x84bc18de13684e84 0x1fa389c33c0cc0c0 0x51fa389c33c0cc0c

def z655 : W := mkw 0x0009028500000000 0x0000902850000000 0x102f800700000002 0x0102f80070000000

def z656 : W := mkw 0xcff26d7af6a0fc02 0x0cff26d7af6a0fc0 0xefd07ff8ffe0fe0d 0xfefd07ff8ffe0fe0

def z657 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb18f8bc70300cfc5 0x0b18f8bc70300cfc

def z658 : W := mkw 0x42000d680420fc02 0x042000d680420fc0 0xee000ff83c00fe0c 0xfee000ff83c00fe0

def z659 : W := mkw 0x8d7b6297c0000000 0x08d7b6297c000000 0x1ffff007c0000003 0xe1ffff007c000000

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000000133138 0x0600000000013313

def z661 : W := mkw 0x99cff3b573d5000c 0x099cff3b573d5000 0x91cff3f803e00001 0x091cff3f803e0000

def z662 : W := mkw 0x063c3e1ec1711712 0x4063c3e1ec171171 0xee7c7e3fc3f33f3f 0xeee7c7e3fc3f33f3

def z663 : W := mkw 0x0000000800201402 0x0000000080020140 0x8040023803e00e01 0x08040023803e00e0

def z664 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e300c07dc033036 0xe4e300c07dc03303

def z665 : W := mkw 0x1df6d00033d5000c 0x01df6d00033d5000 0x1ffff00003e00003 0xe1ffff00003e0000

def z666 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e100404dc13313e 0xa6e100404dc13313

def z667 : W := mkw 0x6f700d2a9caab4a3 0x06f700d2a9caab4a 0x6e700c3ffcfff1fe 0xf6e700c3ffcfff1f

def z668 : W := mkw 0x4bc48d6837b4ff4a 0x84bc48d6837b4ff4 0xefc00ff83ffcffcd 0xfefc00ff83ffcffc

def z669 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5fa380003fff0008 0x55fa380003fff000

def z670 : W := mkw 0x0000301840611412 0x4000030184061141 0x0040703800e00000 0x00040703800e0000

def z671 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x0e0008003c00c000 0x50e0008003c00c00

def z672 : W := mkw 0x04b480002b1e0008 0x004b480002b1e000 0x5fbf80003f1f000b 0xf5fbf80003f1f000

def z673 : W := mkw 0x0dffc2c523144b48 0x80dffc2c523144b4 0xbffffbc7231ccfcf 0xfbffffbc7231ccfc

def z674 : W := mkw 0x24300002880a00a1 0x024300002880a00a 0x00200003000c00c0 0x000200003000c00c

def z675 : W := mkw 0x0f724c0280000000 0x00f724c028000000 0x1ffffc07c0000007 0xe1ffffc07c000000

def z676 : W := mkw 0x1df6c0003b9e000c 0x01df6c0003b9e000 0x1faf80003f1c000b 0x71faf80003f1c000

def z677 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x8e507fffc0000004 0x88e507fffc000000

def z678 : W := mkw 0x4b400d2814a0b402 0x04b400d2814a0b40 0xcfc00ff81ce03005 0xecfc00ff81ce0300

def z679 : W := mkw 0x008902c522004b40 0x8008902c522004b4 0xa1800bc72300cfcd 0x7a1800bc72300cfc

def z680 : W := mkw 0x263d8e878d1ea3e9 0x8263d8e878d1ea3e 0x7e3f8c07fc1ff1fe 0xf7e3f8c07fc1ff1f

def z681 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xa04c763cc3e03f35 0x0a04c763cc3e03f3

def z682 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x20300c07c01ff1f6 0x020300c07c01ff1f

def z683 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xc05c723803f30e0b 0xac05c723803f30e0

def z684 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e100400fc1ff1f8 0x96e100400fc1ff1f

def z685 : W := mkw 0x89cfe3f563144b48 0x889cfe3f563144b4 0xb1effbff231ccfcf 0x7b1effbff231ccfc

def z686 : W := mkw 0x3ff2cc02be8ea0ad 0x03ff2cc02be8ea0a 0x7fb38c07fc1ff1fe 0xf7fb38c07fc1ff1f

def z687 : W := mkw 0x200000000c0aa0a1 0x0200000000c0aa0a 0x602008073c1ff1fe 0x7602008073c1ff1f

def z688 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xa0000bc7231ccfcc 0x1a0000bc7231ccfc

def z689 : W := mkw 0x0004000001100000 0x0000400000110000 0x000c00000310000b 0x2000c00000310000

def z690 : W := mkw 0x0000201840201412 0x4000020184020141 0x00000438c0003030 0x000000438c000303

def z691 : W := mkw 0x0008221440000000 0x0000822144000000 0x8000063cc0000004 0x08000063cc000000

def z692 : W := mkw 0x108490403bdf4b4c 0x8108490403bdf4b4 0x600000003fffcfc8 0x1600000003fffcfc

def z693 : W := mkw 0x02000c0000000000 0x002000c000000000 0x0e000c0000000004 0xe0e000c000000000

def z694 : W := mkw 0x4bc00d6832a05c02 0x04bc00d6832a05c0 0x8fc00ff803e00e05 0xe8fc00ff803e00e0

def z695 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x11af89c7201cc1c2 0x511af89c7201cc1c

def z696 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xa1c00ff803e0fe05 0x0a1c00ff803e0fe0

def z697 : W := mkw 0x20000002800000a1 0x020000002800000a 0x00000007c00001f0 0x000000007c00001f

def z698 : W := mkw 0x5df6d1683bff5c0e 0x05df6d1683bff5c0 0xdffff3f83fff0e0b 0xfdffff3f83fff0e0

def z699 : W := mkw 0x5df6d0483ffffc0e 0x05df6d0483ffffc0 0x7ffff0003ffffe0b 0xf7ffff0003ffffe0

def z700 : W := mkw 0x000c321441510310 0x4000c32144151031 0x805c763cc0130137 0xa805c763cc013013

def z701 : W := mkw 0x0000004000004800 0x0000000400000480 0xa0000bc00000ce04 0x0a0000bc00000ce0

def z702 : W := mkw 0x1942500010c10004 0x01942500010c1000 0x0040700000e00000 0x00040700000e0000

def z703 : W := mkw 0x0008321c40611412 0x40008321c4061141 0xc05c763cc0e33037 0xac05c763cc0e3303

def z704 : W := mkw 0x0008221c40201402 0x00008221c4020140 0xe05c763cc3e03e0f 0xae05c763cc3e03e0

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200803200cc0c0 0x500200803200cc0c

def z706 : W := mkw 0x0080000032800000 0x0008000003280000 0x400000003fe00008 0x1400000003fe0000

def z707 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00ff83ff3ff3d 0xfefc00ff83ff3ff3

def z708 : W := mkw 0x8d7b63b540000000 0x08d7b63b54000000 0x9fdff3f800000001 0x89fdff3f80000000

def z709 : W := mkw 0x0004301841711712 0x4000430184171171 0x6050743cc3f33f3e 0xa6050743cc3f33f3

def z710 : W := mkw 0x1d76d00019df000c 0x01d76d00019df000 0x5e7ff0001fff000b 0xa5e7ff0001fff000

def z711 : W := mkw 0x8d7b63b7c0000000 0x08d7b63b7c000000 0x91eff3fb00000001 0x091eff3fb0000000

def z712 : W := mkw 0x008180c122044b48 0x8008180c122044b4 0x31a389c3200ccfc0 0x531a389c3200ccfc

def z713 : W := mkw 0x1d7b52c518cb4b44 0x81d7b52c518cb4b4 0xee507bc71ce3cfc4 0x8ee507bc71ce3cfc

def z714 : W := mkw 0x8f7b6fb7c80a0000 0x08f7b6fb7c80a000 0xdfffffffdc030007 0xedfffffffdc03000

def z715 : W := mkw 0x0004301841711712 0x4000430184171171 0x40507438c3e33e30 0x840507438c3e33e3

def z716 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xdfffffffc0033037 0xedfffffffc003303

def z717 : W := mkw 0x8f734da380000000 0x08f734da38000000 0x9ffffffb00000007 0xe9ffffffb0000000

def z718 : W := mkw 0xc2092fffc420ff42 0x8c2092fffc420ff4 0xa0000fffc000ffc4 0x0a0000fffc000ffc

def z719 : W := mkw 0xab4b6fb7c400a0a1 0x0ab4b6fb7c400a0a 0xb1cfffffc000f1f5 0x0b1cfffffc000f1f

def z720 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0xb1effbff201cc1cf 0x7b1effbff201cc1c

def z721 : W := mkw 0x1df6d0403bdf4b4c 0x81df6d0403bdf4b4 0x7ffff8073fffcfcf 0xf7ffff8073fffcfc

def z722 : W := mkw 0x09c0004832a05c02 0x009c0004832a05c0 0xefc00ff83fe0fe0d 0xfefc00ff83fe0fe0

def z723 : W := mkw 0x0008321c40611712 0x40008321c4061171 0xe050763cc3e33f3d 0xae050763cc3e33f3

def z724 : W := mkw 0x0084904823755f5a 0xc0084904823755f5 0x6000000003f33f38 0x06000000003f33f3

def z725 : W := mkw 0x3bc6dc02b7d5a0ad 0x03bc6dc02b7d5a0a 0x31cffc07c3e0f1f5 0x031cffc07c3e0f1f

def z726 : W := mkw 0x1436d000095f000c 0x01436d000095f000 0x5e7ff0003fff000b 0xf5e7ff0003fff000

def z727 : W := mkw 0x8d7b63b7c0000000 0x08d7b63b7c000000 0x91fffbffc0000007 0x691fffbffc000000

def z728 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0x605c743cc3f33f3a 0x8605c743cc3f33f3

def z729 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xafc00ff83fe0fe05 0x5afc00ff83fe0fe0

def z730 : W := mkw 0x8b4b6fb7c0000000 0x08b4b6fb7c000000 0x91cffbfb00000001 0x091cffbfb0000000

def z731 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fdfffffc0000005 0x89fdfffffc000000

def z732 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe07c763ce3ff3f3f 0xfe07c763ce3ff3f3

def z733 : W := mkw 0x1df6d1203bdf000c 0x01df6d1203bdf000 0xdffff3f83fff000b 0xfdffff3f83fff000

def z734 : W := mkw 0x4b400d2814a0b402 0x04b400d2814a0b40 0xefc00ff81fe03e0d 0xeefc00ff81fe03e0

def z735 : W := mkw 0x8d7b63b540000000 0x08d7b63b54000000 0x9ffff7fcc0000007 0xe9ffff7fcc000000

def z736 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefe00ff83ffcfe0f 0xfefe00ff83ffcfe0

def z737 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91eff3f800000003 0x691eff3f80000000

def z738 : W := mkw 0x26bd8ec7af1eebe9 0x826bd8ec7af1eebe 0xdf9f87c0df033e31 0x8df9f87c0df033e3

def z739 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0x9fffffffdc000007 0xe9fffffffdc00000

def z740 : W := mkw 0x1dfae21c7aae171e 0x41dfae21c7aae171 0xbfa3863cfc0c3f34 0x5bfa3863cfc0c3f3

def z741 : W := mkw 0x8b4b6fb540000000 0x08b4b6fb54000000 0x9fcff7f800000001 0x89fcff7f80000000

def z742 : W := mkw 0x000d329d41711712 0x4000d329d4171171 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z743 : W := mkw 0x8f775dab81711712 0x48f775dab8171171 0x7fa389c303f33f38 0x47fa389c303f33f3

def z744 : W := mkw 0xaf7b6fb7c400a0a1 0x0af7b6fb7c400a0a 0x9fffffffc0003037 0xe9fffffffc000303

def z745 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xdfdff7f8dc033031 0x8dfdff7f8dc03303

def z746 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8bc7031ccfc7 0x0b1af8bc7031ccfc

def z747 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e300807fc1ff1fa 0x56e300807fc1ff1f

def z748 : W := mkw 0x8d7b63b5480a0000 0x08d7b63b5480a000 0xdffff3f83c1f000b 0xfdffff3f83c1f000

def z749 : W := mkw 0x928dbfb7fbdf000c 0x0928dbfb7fbdf000 0xc0000fffffff000c 0x1c0000fffffff000

def z750 : W := mkw 0xa94b63b54c0aa0a1 0x0a94b63b54c0aa0a 0xf1cff3f83c1ff1f9 0x1f1cff3f83c1ff1f

def z751 : W := mkw 0xc4bb62dff6a0fc02 0x0c4bb62dff6a0fc0 0x703ff007ffe0fe0a 0x1703ff007ffe0fe0

def z752 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xfffffffffc0cf0cf 0xffffffffffc0cf0c

def z753 : W := mkw 0x42800d6836a0fc02 0x042800d6836a0fc0 0xee000ff83fe0fe0c 0xfee000ff83fe0fe0

def z754 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af8bc7231ccfc3 0x591af8bc7231ccfc

def z755 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0xcfc003f81fe00e01 0x8cfc003f81fe00e0

def z756 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x5feff0003ffc000b 0xf5feff0003ffc000

def z757 : W := mkw 0x0b400d280420b402 0x00b400d280420b40 0xefc00ff83fe0fe0d 0xfefc00ff83fe0fe0

def z758 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fcff3f800000001 0x09fcff3f80000000

def z759 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefdc7ff83fe0fe0f 0xfefdc7ff83fe0fe0

def z760 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff4003fff300f 0xf7ffff4003fff300

def z761 : W := mkw 0x1df6d0403bdf480c 0x01df6d0403bdf480 0x7ffff0003fffce0b 0xf7ffff0003fffce0

def z762 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0x8fc003f81fe00e01 0x08fc003f81fe00e0

def z763 : W := mkw 0x263c3e1ecd7bb7b3 0x4263c3e1ecd7bb7b 0x8e6c7a3b3feccec1 0x58e6c7a3b3feccec

def z764 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e100c07fc1ff1fc 0x96e100c07fc1ff1f

def z765 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xbfffffffc000c1c7 0xebfffffffc000c1c

def z766 : W := mkw 0x3df6d002bbdf00ad 0x03df6d002bbdf00a 0x5ffff0033fff00cb 0xf5ffff0033fff00c

def z767 : W := mkw 0x008d82c533944b48 0x8008d82c533944b4 0xf1af8bc73ffccfcf 0x7f1af8bc73ffccfc

def z768 : W := mkw 0x008db2d563554b58 0xc008db2d563554b5 0xb1ffffffe31fcfff 0xfb1ffffffe31fcff

def z769 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5fdff0003fff0009 0x95fdff0003fff000

def z770 : W := mkw 0x5084904837f5fc0e 0x05084904837f5fc0 0x600000003fe0fe08 0x1600000003fe0fe0

def z771 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xffffffffdc13313f 0xeffffffffdc13313

def z772 : W := mkw 0x008580c123144b48 0x8008580c123144b4 0x31af89c3231ccfcb 0x731af89c3231ccfc

def z773 : W := mkw 0x8b4b6fb7c0000000 0x08b4b6fb7c000000 0x91efffffc0000007 0x691efffffc000000

def z774 : W := mkw 0xa2092fbfc420b7b3 0x4a2092fbfc420b7b 0xa0000fffc000fff4 0x0a0000fffc000fff

def z775 : W := mkw 0x6bc00d6ab6a0fca3 0x06bc00d6ab6a0fca 0xefc00ff8ffe0fe3d 0xfefc00ff8ffe0fe3

def z776 : W := mkw 0x82092fb7c0000000 0x082092fb7c000000 0x91ffffffc0000007 0xe91ffffffc000000

def z777 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xee400ff83fe0fe0c 0x9ee400ff83fe0fe0

def z778 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5fdff0003fe30009 0xf5fdff0003fe3000

def z779 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xee5c763cfff33f3f 0xfee5c763cfff33f3

def z780 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xffffffffc000300f 0xeffffffffc000300

def z781 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00bf83fe0fe09 0x5efc00bf83fe0fe0

def z782 : W := mkw 0x008d92c523554b58 0xc008d92c523554b5 0xb1af8bc7231fcfff 0x7b1af8bc7231fcff

def z783 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xbfffffffc3000e0f 0xebfffffffc3000e0

def z784 : W := mkw 0x008da2d563144b58 0xc008da2d563144b5 0xb1af8bc7e31ccfff 0x7b1af8bc7e31ccff

def z785 : W := mkw 0x14b6d0003bdf000c 0x014b6d0003bdf000 0x5e3ff0003fff000a 0xf5e3ff0003fff000

def z786 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1bf8bc7e31fcfff 0x7b1bf8bc7e31fcff

def z787 : W := mkw 0x4bcc3f7477d1eb10 0x44bcc3f7477d1eb1 0x0f9c79c4fc13c132 0x50f9c79c4fc13c13

def z788 : W := mkw 0x0942412000000000 0x0094241200000000 0x91cff3f800000001 0x091cff3f80000000

def z789 : W := mkw 0x508490483fffff1e 0x4508490483fffff1 0x600000003fffff38 0x1600000003fffff3

def z790 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xcfc00ff81fe03e05 0xecfc00ff81fe03e0

def z791 : W := mkw 0x1df6d0403bdf480c 0x01df6d0403bdf480 0x5ffff9c03fffc00b 0xf5ffff9c03fffc00

def z792 : W := mkw 0x0009229540000000 0x0000922954000000 0x91dff7fcc0000007 0xa91dff7fcc000000

def z793 : W := mkw 0x0d72400010800000 0x00d7240001080000 0x5ffff0001ce00003 0xe5ffff0001ce0000

def z794 : W := mkw 0x5bc2cd6836a4fc0e 0x05bc2cd6836a4fc0 0xffc38ff83fe0fe0d 0xfffc38ff83fe0fe0

def z795 : W := mkw 0x8f7b6fb7c400a000 0x08f7b6fb7c400a00 0xfffffffffc13f13f 0xffffffffffc13f13

def z796 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91cffbff00000005 0x091cffbff0000000

def z797 : W := mkw 0x008180c122044848 0x8008180c12204484 0xb1a38bc3200ccec4 0x5b1a38bc3200ccec

def z798 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c763cc3e33f35 0x8e05c763cc3e33f3

def z799 : W := mkw 0x8f7b6fb7c400a000 0x08f7b6fb7c400a00 0xdfffffffdc003007 0xedfffffffdc00300

def z800 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xbffffffffc0cf1f7 0xfbffffffffc0cf1f

def z801 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00ffcffe0ff3d 0xfefc00ffcffe0ff3

def z802 : W := mkw 0x000d329d41711712 0x4000d329d4171171 0xe05c7fffc3f33f3f 0xae05c7fffc3f33f3

def z803 : W := mkw 0xaf7b6fb7c00000a1 0x0af7b6fb7c00000a 0x9fffffffc00001f7 0xe9fffffffc00001f

def z804 : W := mkw 0x49c0016836a0fc02 0x049c0016836a0fc0 0xefc003f83fe0fe09 0xfefc003f83fe0fe0

def z805 : W := mkw 0x6df0016abaaa5ca3 0x06df0016abaaa5ca 0x81f003ffc3ff0ff3 0x081f003ffc3ff0ff

def z806 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x1feff0003ffc000b 0x71feff0003ffc000

def z807 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xf1af8fc7231cffcf 0xff1af8fc7231cffc

def z808 : W := mkw 0x0f7b4fa500000000 0x00f7b4fa50000000 0x9fffffff00000007 0xe9fffffff0000000

def z809 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c7638c3e33e3d 0xae05c7638c3e33e3

def z810 : W := mkw 0x8f736db3c0000000 0x08f736db3c000000 0x1ffffdfbc0000003 0xe1ffffdfbc000000

def z811 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x1ffffdffc0000002 0xc1ffffdffc000000

def z812 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x7fbf8c07fc1ff1ff 0xf7fbf8c07fc1ff1f

def z813 : W := mkw 0xad7b63b7c80a00a1 0x0ad7b63b7c80a00a 0x91fff3ffc01f01f3 0x091fff3ffc01f01f

def z814 : W := mkw 0x04b490002b5f0008 0x004b490002b5f000 0x5ffff0003fff000b 0xf5ffff0003fff000

def z815 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8bc3231ccfc9 0x5b1af8bc3231ccfc

def z816 : W := mkw 0x3df6d002bbdf00ad 0x03df6d002bbdf00a 0x7ffff807ffffc1ff 0xf7ffff807ffffc1f

def z817 : W := mkw 0x26392e97cc0aa0a1 0x026392e97cc0aa0a 0xfffffffffc1ff1ff 0xffffffffffc1ff1f

def z818 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe07c763fc3ff3fff 0xae07c763fc3ff3ff

def z819 : W := mkw 0x008982c522044b48 0x8008982c522044b4 0xb1a38bc7201ccfce 0x7b1a38bc7201ccfc

def z820 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xbfffffffc0003137 0xebfffffffc000313

def z821 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5feff0003fec0009 0xf5feff0003fec000

def z822 : W := mkw 0x0bc00d6032804800 0x00bc00d603280480 0xefc00ff83fe0ce0d 0xfefc00ff83fe0ce0

def z823 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x5fcff0001fe00001 0x85fcff0001fe0000

def z824 : W := mkw 0x5636dd680d7ffc0e 0x05636dd680d7ffc0 0xb03ffff8001ffe06 0x0b03ffff8001ffe0

def z825 : W := mkw 0x243db297c95f03f9 0xc243db297c95f03f 0x103ff007c01f01f2 0x0103ff007c01f01f

def z826 : W := mkw 0x26300d228c0aa0a1 0x026300d228c0aa0a 0xee300ffffc1ff1fe 0xfee300ffffc1ff1f

def z827 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x4e300c07fc1ff1f2 0xd4e300c07fc1ff1f

def z828 : W := mkw 0x8d7b63b7c0000000 0x08d7b63b7c000000 0x9ffff3ffc0000003 0xe9ffff3ffc000000

def z829 : W := mkw 0x008da2d563144b48 0x8008da2d563144b4 0xb1effbff231ccfcf 0x7b1effbff231ccfc

def z830 : W := mkw 0x8f7b6fb7c0000340 0x88f7b6fb7c000034 0x9fffffffc00001c7 0xe9fffffffc00001c

def z831 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91cffbf800000005 0x691cffbf80000000

def z832 : W := mkw 0x1df2d0003acf000c 0x01df2d0003acf000 0x5ffff0003cef0003 0xf5ffff0003cef000

def z833 : W := mkw 0xa43f7297c95b03b1 0x4a43f7297c95b03b 0x103ff007c01f01f2 0x0103ff007c01f01f

def z834 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0xefc00bf83fe0ce0d 0xfefc00bf83fe0ce0

def z835 : W := mkw 0x0d765000095b0000 0x00d765000095b000 0x5ffff0003fff000b 0xf5ffff0003fff000

def z836 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xdffffffffc0ff0f7 0xfdffffffffc0ff0f

def z837 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc007f83fe0fe09 0x9efc007f83fe0fe0

def z838 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xafc00bf83fe0ce0d 0x7afc00bf83fe0ce0

def z839 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91dff7f8c0000001 0x891dff7f8c000000

def z840 : W := mkw 0x008580c123144848 0x8008580c12314484 0xb1af8bc3231ccecf 0x7b1af8bc3231ccec

def z841 : W := mkw 0x7ff2cd62be8ee8ad 0x07ff2cd62be8ee8a 0x1fa389c33c0cc0c0 0x51fa389c33c0cc0c

def z842 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefd00ff8ffe3fe3d 0xfefd00ff8ffe3fe3

def z843 : W := mkw 0x4bc08d6836a4fc4a 0x84bc08d6836a4fc4 0xefc00ff83fecfecd 0xfefc00ff83fecfec

def z844 : W := mkw 0xaf727d3acc6bb4b3 0x4af727d3acc6bb4b 0x4e507438dce33030 0x84e507438dce3303

def z845 : W := mkw 0x0d72412000000000 0x00d7241200000000 0x9ffff3f800000003 0xe9ffff3f80000000

def z846 : W := mkw 0x0df240003a8a0000 0x00df240003a8a000 0x5ffff0003fff000b 0xf5ffff0003fff000

def z847 : W := mkw 0x1df6d0403bdf480c 0x01df6d0403bdf480 0xdffff3c03fff0e0b 0xfdffff3c03fff0e0

def z848 : W := mkw 0x8f7b6fb7c400a000 0x08f7b6fb7c400a00 0xbfffffffc000f007 0xebfffffffc000f00

def z849 : W := mkw 0xaf7b6fb7c80a00a1 0x0af7b6fb7c80a00a 0xdffffffffc1f01ff 0xfdffffffffc1f01f

def z850 : W := mkw 0x8f7b6fb540000000 0x08f7b6fb54000000 0x9ffffff800000007 0xe9ffffff80000000

def z851 : W := mkw 0x0b424d2000000000 0x00b424d200000000 0x9fcffff800000005 0xe9fcffff80000000

def z852 : W := mkw 0x1df6d00033d5000c 0x01df6d00033d5000 0x5ffff0003fe0000b 0xf5ffff0003fe0000

def z853 : W := mkw 0x863b6fb7c0000000 0x0863b6fb7c000000 0x91bfffffc0000007 0x691bfffffc000000

def z854 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefd00ffcffe0fe0f 0xfefd00ffcffe0fe0

def z855 : W := mkw 0xc2092fbfc420b402 0x0c2092fbfc420b40 0x80000fffc0003004 0x080000fffc000300

def z856 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff400ffff303b 0xf5ffff400ffff303

def z857 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff0001fe30003 0xe5ffff0001fe3000

def z858 : W := mkw 0x008902c522004800 0x0008902c52200480 0xb1af8bc7231ccfcf 0x7b1af8bc7231ccfc

def z859 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1a38bc7231ccfcc 0x5b1a38bc7231ccfc

def z860 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x1ffff0003fff0003 0x51ffff0003fff000

def z861 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x1fcff0001fe00001 0x01fcff0001fe0000

def z862 : W := mkw 0x6bc00d6ab6a0fca3 0x06bc00d6ab6a0fca 0xefe00ffffffcffff 0xfefe00ffffffcfff

def z863 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00ffc3ff0ff0f 0xfefc00ffc3ff0ff0

def z864 : W := mkw 0x0004100801711402 0x0000410080171140 0xe05c763cc3f33f3f 0xae05c763cc3f33f3

def z865 : W := mkw 0x1d76500019db0004 0x01d76500019db000 0x5ffff0001ff3000b 0xe5ffff0001ff3000

def z866 : W := mkw 0x008da2d563144b48 0x8008da2d563144b4 0xb1af8fffe31ccfcf 0x7b1af8fffe31ccfc

def z867 : W := mkw 0x943ff297c95f034c 0x8943ff297c95f034 0x103ff007c01f01c2 0x0103ff007c01f01c

def z868 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff0073fff01cb 0xf5ffff0073fff01c

def z869 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xdffffffffc1fc0cf 0xfdffffffffc1fc0c

def z870 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9ffffbffc0000003 0x49ffffbffc000000

def z871 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af8bc7230ccec7 0x791af8bc7230ccec

def z872 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9ffffffbc0000001 0xc9ffffffbc000000

def z873 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5fdff0001ff3000b 0xa5fdff0001ff3000

def z874 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c7e3ce3f3ff3f 0xfe05c7e3ce3f3ff3

def z875 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff0003fef0001 0xd5ffff0003fef000

def z876 : W := mkw 0x0b492fb540000000 0x00b492fb54000000 0x9fffffffc0000007 0xe9fffffffc000000

def z877 : W := mkw 0x000d82c501144b48 0x8000d82c501144b4 0xb1af8bc7001ccfc7 0x6b1af8bc7001ccfc

def z878 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91dff3f800000003 0xa91dff3f80000000

def z879 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0xdffff6383fff000f 0xfdffff6383fff000

def z880 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefe00fff3fe0fe0f 0xfefe00fff3fe0fe0

def z881 : W := mkw 0x8d7b63b7c0000000 0x08d7b63b7c000000 0x91fff7ffc0000007 0xa91fff7ffc000000

def z882 : W := mkw 0x0008321c40611412 0x40008321c4061141 0xe05c763cc3e33e3f 0xae05c763cc3e33e3

def z883 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e200c07fc1ff1fc 0x56e200c07fc1ff1f

def z884 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xdfffffffc013000f 0xedfffffffc013000

def z885 : W := mkw 0x1df2c0003a8e000c 0x01df2c0003a8e000 0x5ffff0003fec000b 0xf5ffff0003fec000

def z886 : W := mkw 0x4084904837f5ff5a 0xc4084904837f5ff5 0x600000003ffffff8 0x1600000003ffffff

def z887 : W := mkw 0x0081b0d962655c5a 0xc0081b0d962655c5 0x51f3fdfbe0eff0f0 0xd51f3fdfbe0eff0f

def z888 : W := mkw 0xaf7b6fb7c80a00a1 0x0af7b6fb7c80a00a 0xbfffffffe01fc1ff 0xfbfffffffe01fc1f

def z889 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff0043fff010f 0xf7ffff0043fff010

def z890 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff0003fffc1cb 0xf7ffff0003fffc1c

def z891 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00ff83ffcffcd 0xfefc00ff83ffcffc

def z892 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e300407fc1ff1fa 0x96e300407fc1ff1f

def z893 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0x9feffbfb3c0cc0c1 0x59feffbfb3c0cc0c

def z894 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefd00ff83ff3fe0f 0xfefd00ff83ff3fe0

def z895 : W := mkw 0x8b4b6fb7c0000000 0x08b4b6fb7c000000 0x91dfffffc0000007 0xa91dfffffc000000

def z896 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fdffff8c0000005 0xe9fdffff8c000000

def z897 : W := mkw 0x8ff6ed72e3144b48 0x88ff6ed72e3144b4 0x2e507438e31ccfc8 0x92e507438e31ccfc

def z898 : W := mkw 0x708490483ffffcaf 0x0708490483ffffca 0x600000003ffffff8 0x1600000003ffffff

def z899 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff0003cff0002 0xd5ffff0003cff000

def z900 : W := mkw 0x0084904823755f5a 0xc0084904823755f5 0x60300c07e3fffffe 0xf60300c07e3fffff

def z901 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0x9ffffffffc1fc1f7 0xf9ffffffffc1fc1f

def z902 : W := mkw 0x4bc08d6836a4fc0a 0x04bc08d6836a4fc0 0xffe38ff83fecfe0d 0xfffe38ff83fecfe0

def z903 : W := mkw 0x5084904833f55c0e 0x05084904833f55c0 0x0000000003e00e00 0x00000000003e00e0

def z904 : W := mkw 0x000d329d41711712 0x4000d329d4171171 0xf1dff7fcc3f33f3f 0xaf1dff7fcc3f33f3

def z905 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff8033fffc0cb 0xf5ffff8033fffc0c

def z906 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff8073fff000f 0xf5ffff8073fff000

def z907 : W := mkw 0x6bc00d6836a0fca3 0x06bc00d6836a0fca 0xefc00ff83fe0fffd 0xfefc00ff83fe0fff

def z908 : W := mkw 0x8d7b63b540000000 0x08d7b63b54000000 0x91fff3f800000003 0x091fff3f80000000

def z909 : W := mkw 0x000db29d4175175a 0xc000db29d4175175 0xf07ffe3fe3ffffff 0xff07ffe3fe3fffff

def z910 : W := mkw 0x0000301840611412 0x4000030184061141 0xc0507638c3e33e31 0x8c0507638c3e33e3

def z911 : W := mkw 0x208490482f7ffffb 0xc208490482f7ffff 0x600000003ffffff8 0x1600000003ffffff

def z912 : W := mkw 0x000db29d4175175a 0xc000db29d4175175 0xf05ff63cc3f33f3f 0xaf05ff63cc3f33f3

def z913 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefe00ffb3fecfecd 0xfefe00ffb3fecfec

def z914 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fffffffe00cc0c7 0xf9fffffffe00cc0c

def z915 : W := mkw 0x02800c482620fc02 0x002800c482620fc0 0xefc00ff83fe0fe0d 0xfefc00ff83fe0fe0

def z916 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xf1ef8bc723fccfcf 0xff1ef8bc723fccfc

def z917 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0xefb00fc7fc1ff1ff 0xfefb00fc7fc1ff1f

def z918 : W := mkw 0x0f724d200c0aa000 0x00f724d200c0aa00 0xfffffff83c1ff00f 0xffffffff83c1ff00

def z919 : W := mkw 0x008da2d563144b48 0x8008da2d563144b4 0xf1ffffffe31fffff 0xff1ffffffe31ffff

def z920 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9ffffbfb00000003 0xe9ffffbfb0000000

def z921 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xffaf8bc73f1ccfcf 0xfffaf8bc73f1ccfc

def z922 : W := mkw 0xef726d3adcaab4a3 0x0ef726d3adcaab4a 0x4e507438dce33030 0x84e507438dce3303

def z923 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fdff7fcc0000007 0xa9fdff7fcc000000

def z924 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91effbfb00000001 0x491effbfb0000000

def z925 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff404ffff000f 0xf5ffff404ffff000

def z926 : W := mkw 0x0df6500033d10000 0x00df6500033d1000 0x5ffff0003ff3000b 0xf5ffff0003ff3000

def z927 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xdffffffffc1f303f 0xfdffffffffc1f303

def z928 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xeff00fffffffffff 0xfeff00ffffffffff

def z929 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91cff7fcc0000005 0x091cff7fcc000000

def z930 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8bc3230ccecd 0x7b1af8bc3230ccec

def z931 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0xee300e07ff1fffff 0xfee300e07ff1ffff

def z932 : W := mkw 0x4bc24d6836a0fc02 0x04bc24d6836a0fc0 0xffcffff83fe0fe0d 0xfffcffff83fe0fe0

def z933 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fffffffc0130137 0xe9fffffffc013013

def z934 : W := mkw 0x508490483fffff4e 0x8508490483fffff4 0x600000003fffffc8 0x1600000003fffffc

def z935 : W := mkw 0x008580c123144b48 0x8008580c123144b4 0x11a389c3230ccec0 0x511a389c3230ccec

def z936 : W := mkw 0x8f7b6fb7c80a0000 0x08f7b6fb7c80a000 0xfffffffffc1fc1cf 0xffffffffffc1fc1c

def z937 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x91ffffffc0000007 0x091ffffffc000000

def z938 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xffffffffe01ff1ff 0xfffffffffe01ff1f

def z939 : W := mkw 0x008982c522044b48 0x8008982c522044b4 0x91a38bc3200ccec0 0x591a38bc3200ccec

def z940 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xf1bf8bc7231fcfcf 0xff1bf8bc7231fcfc

def z941 : W := mkw 0x0f724d2280000000 0x00f724d228000000 0x9fffffffc0000007 0xe9fffffffc000000

def z942 : W := mkw 0x5df6d1603bdf480c 0x05df6d1603bdf480 0x5ffff1c03fff000b 0xf5ffff1c03fff000

def z943 : W := mkw 0x008580c123144b48 0x8008580c123144b4 0x31a389c7231ccfce 0x731a389c7231ccfc

def z944 : W := mkw 0xc2092fffc420ff12 0x4c2092fffc420ff1 0xa0000fffc000ff34 0x0a0000fffc000ff3

def z945 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c7e3fc3f3ffff 0xae05c7e3fc3f3fff

def z946 : W := mkw 0x008d92c523554b48 0x8008d92c523554b4 0xf1ffffc7e3ffffff 0xff1ffffc7e3fffff

def z947 : W := mkw 0x4b4d8fad15b4b74a 0x84b4d8fad15b4b74 0x5e6f843f1cfc31c2 0x85e6f843f1cfc31c

def z948 : W := mkw 0x0f7a6f3440000000 0x00f7a6f344000000 0x9ffffffcc0000007 0xe9ffffffcc000000

def z949 : W := mkw 0x008da2d563144b48 0x8008da2d563144b4 0xb1bffbc7e31ccfcf 0x7b1bffbc7e31ccfc

def z950 : W := mkw 0x008180c122044848 0x8008180c12204484 0x31a389c3230ccec8 0x531a389c3230ccec

def z951 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xffef8ff83fe0fe0f 0xfffef8ff83fe0fe0

def z952 : W := mkw 0x1df6d0003bdf034c 0x81df6d0003bdf034 0x5ffff0003fff01cb 0xf5ffff0003fff01c

def z953 : W := mkw 0x508490483bff5c0e 0x0508490483bff5c0 0x400000003fff0e08 0x1400000003fff0e0

def z954 : W := mkw 0x108d92c533d54b4c 0x8108d92c533d54b4 0xb1af8bc723fccfcf 0x7b1af8bc723fccfc

def z955 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xbffffffffc1cc1cf 0xfbffffffffc1cc1c

def z956 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe1dc7ffcc3f33f3f 0xee1dc7ffcc3f33f3

def z957 : W := mkw 0x0000301840611412 0x4000030184061141 0x60507438c3e33e38 0x860507438c3e33e3

def z958 : W := mkw 0x8b4b6fb540000000 0x08b4b6fb54000000 0x9fcffbf800000001 0x49fcffbf80000000

def z959 : W := mkw 0xaf7b6fb7c400a0a1 0x0af7b6fb7c400a0a 0xbfffffffe01cf1ff 0xfbfffffffe01cf1f

def z960 : W := mkw 0x1df6d0403bdf480c 0x01df6d0403bdf480 0xfffffbc73fffcfcf 0xffffffbc73fffcfc

def z961 : W := mkw 0x1d72500018cb0004 0x01d72500018cb000 0x5ffff0003cff000b 0xf5ffff0003cff000

def z962 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fbfffffc0000006 0x49fbfffffc000000

def z963 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5fbff0003fff000a 0x55fbff0003fff000

def z964 : W := mkw 0x008db2d563554b58 0xc008db2d563554b5 0xf1bfffc7e31fffff 0xff1bfffc7e31ffff

def z965 : W := mkw 0x8f7b6fb7c0000300 0x08f7b6fb7c000030 0xbfffffffc0000f07 0xebfffffffc0000f0

def z966 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5e7ff0003fff000a 0x95e7ff0003fff000

def z967 : W := mkw 0x09c2400032800000 0x009c240003280000 0x5fcff0003fe00009 0xf5fcff0003fe0000

def z968 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8bc7201ccfc6 0x5b1af8bc7201ccfc

def z969 : W := mkw 0x8f7b6fb7c80a0000 0x08f7b6fb7c80a000 0x9ffffffffc0c0007 0xf9ffffffffc0c000

def z970 : W := mkw 0x8d7b63b540000000 0x08d7b63b54000000 0x9ffffbff00000007 0xe9ffffbff0000000

def z971 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91cff3fc00000007 0x291cff3fc0000000

def z972 : W := mkw 0x22092edfc420fff3 0xc22092edfc420fff 0xa0000fffc000fff4 0x0a0000fffc000fff

def z973 : W := mkw 0x8d7b63b7c0000000 0x08d7b63b7c000000 0x91dff3f8c0000001 0x091dff3f8c000000

def z974 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffffc07fffff1ff 0xf7ffffc07fffff1f

def z975 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff0001fff0003 0x85ffff0001fff000

def z976 : W := mkw 0x0008221c40201402 0x00008221c4020140 0xe05c763cc3f33f3f 0xae05c763cc3f33f3

def z977 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xbfffffffc010010f 0xebfffffffc010010

def z978 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x91af8bc3231ccecb 0x791af8bc3231ccec

def z979 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xbfffffffc01ff1f7 0xebfffffffc01ff1f

def z980 : W := mkw 0x008580c123144b48 0x8008580c123144b4 0xb1a38bc3231ccfcd 0x7b1a38bc3231ccfc

def z981 : W := mkw 0x7f725d2a9cebb4a7 0x07f725d2a9cebb4a 0x4e507438dce33030 0x84e507438dce3303

def z982 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xf1fff63cc3f33f3f 0xef1fff63cc3f33f3

def z983 : W := mkw 0x8f7b6fb7c80a0000 0x08f7b6fb7c80a000 0xfffffffffc1f313f 0xffffffffffc1f313

def z984 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5ffff004ffff013b 0xf5ffff004ffff013

def z985 : W := mkw 0x06392e97c0000000 0x006392e97c000000 0x9fffffffc0000007 0xe9fffffffc000000

def z986 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0xfffff2003fff0e0f 0xffffff2003fff0e0

def z987 : W := mkw 0x09c4900033d50008 0x009c4900033d5000 0x5ffff0003fff000b 0xf5ffff0003fff000

def z988 : W := mkw 0x19cff2dd73f55f5e 0xc19cff2dd73f55f5 0x91cff3f803e00e01 0x091cff3f803e00e0

def z989 : W := mkw 0x8b4b6fb540000000 0x08b4b6fb54000000 0x9fefffff00000007 0xe9fefffff0000000

def z990 : W := mkw 0x8f7b6fb7c400a000 0x08f7b6fb7c400a00 0xfffffffffc1cf1cf 0xffffffffffc1cf1c

def z991 : W := mkw 0x8b4b6fb7c0000000 0x08b4b6fb7c000000 0x91cff7f8c0000001 0x091cff7f8c000000

def z992 : W := mkw 0x1df6d0003bdf030c 0x01df6d0003bdf030 0x7ffff0003fff0f0b 0xf7ffff0003fff0f0

def z993 : W := mkw 0x0009229540000000 0x0000922954000000 0x91effbff00000007 0x691effbff0000000

def z994 : W := mkw 0x26b49c4aaf7ffffb 0xc26b49c4aaf7ffff 0x6e300c07fffffffe 0xf6e300c07fffffff

def z995 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fffffffe01c000f 0xf9fffffffe01c000

def z996 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1bf8fc7e31ccfcf 0xfb1bf8fc7e31ccfc

def z997 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9feffbff00000007 0x69feffbff0000000

def z998 : W := mkw 0x008982c522044848 0x8008982c52204484 0xb1af8bc7230ccecf 0x7b1af8bc7230ccec

def z999 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c763ce3ffffff 0xbe05c763ce3fffff

def z1000 : W := mkw 0x6bc00d6ab6a0fca3 0x06bc00d6ab6a0fca 0xefd00ffffff3ffff 0xfefd00ffffff3fff

def z1001 : W := mkw 0x1d76d00019df000c 0x01d76d00019df000 0x5e7ff0003cff000a 0xf5e7ff0003cff000

def z1002 : W := mkw 0x0df6c00033940008 0x00df6c0003394000 0x5ffff0003ffc000b 0xf5ffff0003ffc000

def z1003 : W := mkw 0x8f7b6fb7cc0aa000 0x08f7b6fb7cc0aa00 0xfffffffffc1ff00f 0xffffffffffc1ff00

def z1004 : W := mkw 0x4bc00d6ab6a0fc02 0x04bc00d6ab6a0fc0 0xefc00fffffe0fe0d 0xfefc00fffffe0fe0

def z1005 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9ffff7ffc0000003 0x89ffff7ffc000000

def z1006 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xcfc007f83fe03e09 0xfcfc007f83fe03e0

def z1007 : W := mkw 0x0004301841711712 0x4000430184171171 0xe0507638c3f33f3d 0xae0507638c3f33f3

def z1008 : W := mkw 0xaf7b6fb7c80a00a1 0x0af7b6fb7c80a00a 0x9fffffffc00c00c7 0xe9fffffffc00c00c

def z1009 : W := mkw 0x8b4b6fb540000000 0x08b4b6fb54000000 0x91cffff800000005 0x091cffff80000000

def z1010 : W := mkw 0x1d72500018cb0004 0x01d72500018cb000 0x5fdff0001ce30001 0x85fdff0001ce3000

def z1011 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x1ffff0003fec0003 0xf1ffff0003fec000

def z1012 : W := mkw 0x000cb21c4175175a 0xc000cb21c4175175 0xe05c763cc3ff3fff 0xae05c763cc3ff3ff

def z1013 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0x8fc003f83fe00e01 0x58fc003f83fe00e0

def z1014 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xfffffffffc03f03f 0xffffffffffc03f03

def z1015 : W := mkw 0x0084904823755f5a 0xc0084904823755f5 0x0000000003e00e00 0x00000000003e00e0

def z1016 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00fff3fe0ffcd 0xfefc00fff3fe0ffc

def z1017 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc007f81fe03e0d 0xaefc007f81fe03e0

def z1018 : W := mkw 0x008982c522044b48 0x8008982c522044b4 0xb1a38bc7230ccfcd 0x7b1a38bc7230ccfc

def z1019 : W := mkw 0x8f7b6fb7d0800000 0x08f7b6fb7d080000 0xdfffffffdce00007 0xedfffffffdce0000

def z1020 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x9fcff3f800000001 0xe9fcff3f80000000

def z1021 : W := mkw 0x1df6d0003bdf031c 0x41df6d0003bdf031 0x5ffff0003fff013b 0xf5ffff0003fff013

def z1022 : W := mkw 0xaf7b6fb7c80a00a1 0x0af7b6fb7c80a00a 0xffffffffc01f31ff 0xeffffffffc01f31f

def z1023 : W := mkw 0x19c6d0003bdf000c 0x019c6d0003bdf000 0x5fcff0003fff0009 0xf5fcff0003fff000

def z1024 : W := mkw 0x008d92c523554b48 0x8008d92c523554b4 0xb1effbc723fccfcf 0x7b1effbc723fccfc

def z1025 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xc05c763cc3f33f33 0x8c05c763cc3f33f3

def z1026 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xdfffffffdc1f31f7 0xedfffffffdc1f31f

def z1027 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xf1af8bc7231fffff 0x7f1af8bc7231ffff

def z1028 : W := mkw 0x8b4b6fb7c0000000 0x08b4b6fb7c000000 0x9fcfffffc0000005 0xe9fcfffffc000000

def z1029 : W := mkw 0x008180c122044848 0x8008180c12204484 0x91a38bc3230ccec1 0x591a38bc3230ccec

def z1030 : W := mkw 0x000d329d41711752 0xc000d329d4171175 0xe05c763fc3f33fff 0xae05c763fc3f33ff

def z1031 : W := mkw 0x1df6d0403bdf484c 0x81df6d0403bdf484 0x5ffff0003fffc0cb 0xf5ffff0003fffc0c

def z1032 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xc05c7638c3f33e3b 0xac05c7638c3f33e3

def z1033 : W := mkw 0x8f726d32c0000000 0x08f726d32c000000 0x9ffffff8c0000007 0xe9ffffff8c000000

def z1034 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xcfc00ff83fe0fe01 0xdcfc00ff83fe0fe0

def z1035 : W := mkw 0x8d7b63b540000000 0x08d7b63b54000000 0x9feff3f800000001 0x49feff3f80000000

def z1036 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0xf1dff7fcc013313f 0xaf1dff7fcc013313

def z1037 : W := mkw 0x008db2d563554b58 0xc008db2d563554b5 0xb1affbc7231ccfcf 0x7b1affbc7231ccfc

def z1038 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff8003fffc00f 0xf7ffff8003fffc00

def z1039 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91eff3ff00000003 0x091eff3ff0000000

def z1040 : W := mkw 0x008d92c523554b48 0x8008d92c523554b4 0xb1bffbc7231fcfcf 0x7b1bffbc7231fcfc

def z1041 : W := mkw 0x008180c122044848 0x8008180c12204484 0xb1a38bc7231ccfcf 0x7b1a38bc7231ccfc

def z1042 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe050763cc3f33f3c 0x8e050763cc3f33f3

def z1043 : W := mkw 0x143ff295495f035c 0xc143ff295495f035 0x103ff007c01f01f2 0x0103ff007c01f01f

def z1044 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e7c7c07fc1ff1ff 0xf6e7c7c07fc1ff1f

def z1045 : W := mkw 0x1d76d00019df000c 0x01d76d00019df000 0x5e5ff0001ce30000 0x85e5ff0001ce3000

def z1046 : W := mkw 0x943ff297c95f031c 0x4943ff297c95f031 0x103ff007c01f0132 0x0103ff007c01f013

def z1047 : W := mkw 0x9f7b6fb7d88a0004 0x09f7b6fb7d88a000 0x9fffffffdc000007 0xe9fffffffdc00000

def z1048 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xefc00ff81fe0fe05 0x8efc00ff81fe0fe0

def z1049 : W := mkw 0x008db2d563554b58 0xc008db2d563554b5 0xf1fffbc7e3ffcfff 0xff1fffbc7e3ffcff

def z1050 : W := mkw 0x843b6297c0000000 0x0843b6297c000000 0x91ffffffc0000007 0xe91ffffffc000000

def z1051 : W := mkw 0x3df6d002bbdf00ad 0x03df6d002bbdf00a 0x7ffff407ffff31ff 0xf7ffff407ffff31f

def z1052 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91ffffffc0000007 0xe91ffffffc000000

def z1053 : W := mkw 0xc2092ffd4420fc02 0x0c2092ffd4420fc0 0xa0000ff80000fe04 0x0a0000ff80000fe0

def z1054 : W := mkw 0x0084904823755f5a 0xc0084904823755f5 0x2000000023fccfc8 0x12000000023fccfc

def z1055 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1ef8fff231ccfcf 0xfb1ef8fff231ccfc

def z1056 : W := mkw 0x108490483bff5f5e 0xc108490483bff5f5 0x600000003ffffff8 0x1600000003ffffff

def z1057 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fefffffc0000005 0x49fefffffc000000

def z1058 : W := mkw 0x000902c500004b40 0x8000902c500004b4 0xb1af8bc7201ccfcf 0x7b1af8bc7201ccfc

def z1059 : W := mkw 0x1d72500018cb0004 0x01d72500018cb000 0x5e7ff0001ce30002 0x85e7ff0001ce3000

def z1060 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91cff7f800000005 0xa91cff7f80000000

def z1061 : W := mkw 0x0000301840611412 0x4000030184061141 0xe050763cc3f33f3f 0xae050763cc3f33f3

def z1062 : W := mkw 0x76b49c4abffffcaf 0x076b49c4abffffca 0x6e300c07fffffffe 0xf6e300c07fffffff

def z1063 : W := mkw 0x2f724d228c0aa0a1 0x02f724d228c0aa0a 0xfffffffffc1ff1ff 0xffffffffffc1ff1f

def z1064 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x2e300c07fc1ff1f6 0x52e300c07fc1ff1f

def z1065 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xbfffffffe000c00f 0xfbfffffffe000c00

def z1066 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xdfffffffc3e0000f 0xedfffffffc3e0000

def z1067 : W := mkw 0x8b4b6fb540000000 0x08b4b6fb54000000 0x9fdffffcc0000007 0xe9fdffffcc000000

def z1068 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0x8fc00ff83fe0ce05 0xf8fc00ff83fe0ce0

def z1069 : W := mkw 0x000db29d4175175a 0xc000db29d4175175 0xf1ffffffc3ff3fff 0xef1ffffffc3ff3ff

def z1070 : W := mkw 0x8f7b6fb7c400a000 0x08f7b6fb7c400a00 0x9ffffffffc00c007 0xf9ffffffffc00c00

def z1071 : W := mkw 0x894b63b7c0000000 0x0894b63b7c000000 0x91cff3ffc0000001 0x091cff3ffc000000

def z1072 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8fc7e31cffff 0x7b1af8fc7e31cfff

def z1073 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0x31af89c7231ccfca 0x531af89c7231ccfc

def z1074 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0xee700e3ffc1ff1ff 0xfee700e3ffc1ff1f

def z1075 : W := mkw 0x000d028501100300 0x0000d02850110030 0xb1af8bc7231ccfcf 0x7b1af8bc7231ccfc

def z1076 : W := mkw 0x04300000080a0000 0x004300000080a000 0x6e300c07fc1ff1fe 0xf6e300c07fc1ff1f

def z1077 : W := mkw 0x0d7b629540000000 0x00d7b62954000000 0x9fffffffc0000007 0xe9fffffffc000000

def z1078 : W := mkw 0x26324c028c0aa0a1 0x026324c028c0aa0a 0x7e3ffc07fc1ff1fe 0xf7e3ffc07fc1ff1f

def z1079 : W := mkw 0x42092ffd4420ff52 0xc42092ffd4420ff5 0xa0000fffc000fff4 0x0a0000fffc000fff

def z1080 : W := mkw 0x6bc00d6ab6a0fca3 0x06bc00d6ab6a0fca 0xefc00ffb3fe0fecd 0xfefc00ffb3fe0fec

def z1081 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x5feff0003fff0009 0x55feff0003fff000

def z1082 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xa05c763cc3f33f37 0x0a05c763cc3f33f3

def z1083 : W := mkw 0x1df6d002bbdf000c 0x01df6d002bbdf000 0x5ffff007ffff000b 0xf5ffff007ffff000

def z1084 : W := mkw 0x26300c028c0aa0a1 0x026300c028c0aa0a 0x6e700c07fffff1ff 0xf6e700c07fffff1f

def z1085 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9feffffb00000005 0xe9feffffb0000000

def z1086 : W := mkw 0xaf7b6fb7c400a0a1 0x0af7b6fb7c400a0a 0xfffffffffc00f1ff 0xffffffffffc00f1f

def z1087 : W := mkw 0xe2092fffc420fca3 0x0e2092fffc420fca 0xa0000fffc000fff4 0x0a0000fffc000fff

def z1088 : W := mkw 0x02000c000400a000 0x002000c000400a00 0x6e300c07fc1ff1fe 0xf6e300c07fc1ff1f

def z1089 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9fffffffc01c01c7 0xe9fffffffc01c01c

def z1090 : W := mkw 0x22000c028c0aa0a1 0x022000c028c0aa0a 0x6e000c07fc1ff1fc 0xf6e000c07fc1ff1f

def z1091 : W := mkw 0x243000028c0aa0a1 0x0243000028c0aa0a 0x6e300007fc1ff1fa 0xf6e300007fc1ff1f

def z1092 : W := mkw 0x008982c522044b48 0x8008982c522044b4 0xb1af8bc7200ccfc7 0x7b1af8bc7200ccfc

def z1093 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xc05c763cc3e33e37 0xac05c763cc3e33e3

def z1094 : W := mkw 0x1d76d00019df000c 0x01d76d00019df000 0x5ffff0001cff0003 0xe5ffff0001cff000

def z1095 : W := mkw 0x0bc00d2832a01402 0x00bc00d2832a0140 0xefc00ff83fe03e0d 0xfefc00ff83fe03e0

def z1096 : W := mkw 0x000cb21c4175171a 0x4000cb21c4175171 0xf07ff63cc3ff3f3f 0xaf07ff63cc3ff3f3

def z1097 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0xdffffbc03fff000f 0xfdffffbc03fff000

def z1098 : W := mkw 0xeff34de3be8ae8a1 0x0eff34de3be8ae8a 0x1fa389c33c0cc0c0 0x51fa389c33c0cc0c

def z1099 : W := mkw 0x56b49c483ffffc0e 0x056b49c483ffffc0 0x6e300c003ffffe0e 0xf6e300c003ffffe0

def z1100 : W := mkw 0x1df250003acb0004 0x01df250003acb000 0x5ffff0003fe3000b 0xf5ffff0003fe3000

def z1101 : W := mkw 0x8f7b6fb7c80a0000 0x08f7b6fb7c80a000 0x9fffffffc01f0007 0xe9fffffffc01f000

def z1102 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xef800ff83fe0fe0c 0x5ef800ff83fe0fe0

def z1103 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe07c7e3fc3f33f3f 0xee07c7e3fc3f33f3

def z1104 : W := mkw 0x8b4b6fb54400a000 0x08b4b6fb54400a00 0xffcffff83c00f00d 0xfffcffff83c00f00

def z1105 : W := mkw 0x4bc00d6836a0fc02 0x04bc00d6836a0fc0 0xcfc00bf83fe0ce09 0xfcfc00bf83fe0ce0

def z1106 : W := mkw 0x3df6d002bbdf00ad 0x03df6d002bbdf00a 0x5ffff000ffff003b 0xf5ffff000ffff003

def z1107 : W := mkw 0x8f7b6fb7c0000310 0x48f7b6fb7c000031 0x9fffffffc0000137 0xe9fffffffc000013

def z1108 : W := mkw 0x42000d680420fc02 0x042000d680420fc0 0xee400ff83fe0fe0d 0xfee400ff83fe0fe0

def z1109 : W := mkw 0xaf7b6fb7cc0aa0a1 0x0af7b6fb7cc0aa0a 0xffffffffdc03f1f7 0xeffffffffdc03f1f

def z1110 : W := mkw 0x008db2d563554b48 0x8008db2d563554b4 0xf1ffffffe3ffcfcf 0xff1ffffffe3ffcfc

def z1111 : W := mkw 0x49cdb3fd73f55f5a 0xc49cdb3fd73f55f5 0x91cff3f803e00e01 0x091cff3f803e00e0

def z1112 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1fffbc7231ccfcf 0xfb1fffbc7231ccfc

def z1113 : W := mkw 0x3df6d0003bdf00ad 0x03df6d0003bdf00a 0x5ffff0003fff01fb 0xf5ffff0003fff01f

def z1114 : W := mkw 0x0009229540000000 0x0000922954000000 0x91cff3f800000001 0x091cff3f80000000

def z1115 : W := mkw 0xaf7b6fb7c80a00a1 0x0af7b6fb7c80a00a 0x9fffffffc0030037 0xe9fffffffc003003

def z1116 : W := mkw 0x0004301841711412 0x4000430184171141 0xe05c7638c3f33e3f 0xae05c7638c3f33e3

def z1117 : W := mkw 0x1df6d0403bdf4b4c 0x81df6d0403bdf4b4 0x5ffff0003fff0e0b 0xf5ffff0003fff0e0

def z1118 : W := mkw 0xcf7b6fb7d480a000 0x0cf7b6fb7d480a00 0x9fffffffdc000007 0xe9fffffffdc00000

def z1119 : W := mkw 0x49c0016832a05c02 0x049c0016832a05c0 0xefc007f83fe03e0d 0xfefc007f83fe03e0

def z1120 : W := mkw 0x0004301841711712 0x4000430184171171 0x605c7438c3f33f3b 0xa605c7438c3f33f3

def z1121 : W := mkw 0x1df6d0403bdf4b4c 0x81df6d0403bdf4b4 0xfffffbc03fffcfcf 0xffffffbc03fffcfc

def z1122 : W := mkw 0x008d92c523554b48 0x8008d92c523554b4 0xf1af8bc723ffcfcf 0x7f1af8bc723ffcfc

def z1123 : W := mkw 0xaf7b6fb7c400a0a1 0x0af7b6fb7c400a0a 0x9fffffffc000c0c7 0xe9fffffffc000c0c

def z1124 : W := mkw 0x4bc00d6832a05c02 0x04bc00d6832a05c0 0xcfc00ff83fe00e0d 0xfcfc00ff83fe00e0

def z1125 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0x9ffff7f8c0000003 0xe9ffff7f8c000000

def z1126 : W := mkw 0x008d82c523144b48 0x8008d82c523144b4 0xb1af8bc7230ccfc5 0x5b1af8bc7230ccfc

def z1127 : W := mkw 0x1df6d0003bdf000c 0x01df6d0003bdf000 0x7ffff0003fff313b 0xf7ffff0003fff313

def z1128 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x1fcff0003fe00001 0x51fcff0003fe0000

def z1129 : W := mkw 0x000d329d41711712 0x4000d329d4171171 0xf07ff63fc3f33f3f 0xaf07ff63fc3f33f3

def z1130 : W := mkw 0x894b63b540000000 0x0894b63b54000000 0x91dff3fcc0000003 0x091dff3fcc000000

def z1131 : W := mkw 0x8f7b6fb7c0000000 0x08f7b6fb7c000000 0xdffffffffc00000f 0xfdffffffffc00000

def z1132 : W := mkw 0x0084804023144808 0x0008480402314480 0xb1af8bc7231ccfcf 0x7b1af8bc7231ccfc

def z1133 : W := mkw 0x0009229540000000 0x0000922954000000 0xf1ffffffe01ff1ff 0xff1ffffffe01ff1f

def z1134 : W := mkw 0x000c321c41711712 0x4000c321c4171171 0xe05c7638c3f33f39 0x8e05c7638c3f33f3

def z1135 : W := mkw 0x4b400d6814a0fc02 0x04b400d6814a0fc0 0xee400ff81fe0fe0d 0xaee400ff81fe0fe0

def z1136 : W := mkw 0xaf7b6fb7c400a0a1 0x0af7b6fb7c400a0a 0xffffffffc013f1ff 0xeffffffffc013f1f

def z1137 : W := mkw 0x19c6d00033d5000c 0x019c6d00033d5000 0x5fdff0003ff3000b 0xf5fdff0003ff3000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z7,z3,z4,z5]),(0,[z8,z0,z1,z7,z3,z9,z5]),(0,[z0,z1,z7,z3,z4,z5,z10]),(0,[z0,z11,z1,z7,z3,z4,z12])],[(0,[z0,z1,z13,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z14,z4,z5]),(0,[z0,z1,z7,z3,z15,z16,z5]),(0,[z0,z1,z7,z3,z4,z5,z17]),(0,[z0,z1,z18,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z19])],[(0,[z0,z20,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z21]),(0,[z0,z1,z22,z7,z3,z4,z5]),(0,[z0,z1,z23,z24,z3,z4,z5]),(0,[z0,z25,z1,z7,z3,z4,z12])],[(0,[z0,z1,z7,z26,z3,z4,z5]),(0,[z0,z27,z1,z28,z3,z4,z5]),(0,[z0,z1,z3,z29,z4,z30,z5])],[(0,[z0,z25,z1,z7,z3,z4,z5]),(1,[z31,z1,z7,z3,z4,z5])],[(0,[z0,z32,z7,z3,z33,z4,z5]),(0,[z34,z0,z1,z7,z3,z4,z5]),(0,[z0,z35,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z36,z5])],[(0,[z0,z1,z37,z3,z4,z30,z5])],[(0,[z0,z1,z7,z3,z38,z4,z5]),(0,[z39,z0,z1,z7,z3,z4,z12]),(0,[z40,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z41,z3,z4,z5])]],
   [[(0,[z42,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z43,z4,z5]),(0,[z0,z1,z7,z3,z4,z44,z5]),(0,[z0,z1,z3,z29,z4,z45,z5]),(0,[z46,z0,z1,z7,z3,z4,z47])],[(0,[z0,z1,z7,z3,z4,z5,z48]),(0,[z39,z0,z1,z7,z3,z4,z5]),(0,[z8,z0,z1,z7,z3,z4,z49]),(0,[z50,z0,z1,z7,z3,z4,z51]),(0,[z0,z1,z7,z3,z4,z52,z47])],[(0,[z0,z1,z53,z7,z3,z4,z5]),(0,[z0,z54,z1,z7,z3,z4,z5]),(0,[z55,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z56,z4,z5]),(1,[z0,z1,z7,z3,z4,z57]),(1,[z0,z1,z58,z7,z3,z59])],[(0,[z0,z1,z7,z3,z4,z60,z5]),(0,[z0,z1,z7,z61,z3,z4,z5]),(0,[z0,z1,z7,z62,z3,z4,z63]),(0,[z39,z0,z1,z37,z3,z4,z5]),(0,[z0,z1,z37,z3,z4,z45,z5]),(0,[z0,z1,z7,z3,z4,z5,z64]),(0,[z0,z65,z1,z66,z3,z4,z5]),(0,[z67,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z68,z4,z5]),(0,[z0,z1,z7,z3,z4,z69,z5])],[(0,[z0,z1,z7,z3,z70,z4,z5]),(0,[z0,z1,z7,z3,z71,z4,z5]),(0,[z0,z1,z72,z7,z3,z4,z12]),(0,[z0,z1,z73,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z74]),(1,[z0,z1,z7,z3,z4,z75])],[(0,[z76,z1,z7,z3,z15,z4,z5]),(0,[z0,z77,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z24,z78,z5])],[(0,[z0,z1,z7,z3,z4,z79,z5]),(0,[z80,z0,z1,z7,z62,z4,z5]),(0,[z81,z0,z1,z7,z3,z4,z5]),(0,[z82,z0,z1,z7,z3,z4,z5]),(0,[z8,z0,z1,z83,z3,z4,z5]),(0,[z0,z1,z7,z83,z3,z4,z5]),(0,[z0,z1,z7,z3,z84,z4,z5])]],
   [[(0,[z85,z0,z1,z7,z3,z4,z5]),(0,[z0,z32,z7,z3,z4,z5,z86]),(0,[z0,z1,z87,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z89,z5]),(0,[z0,z1,z90,z7,z3,z4,z5]),(0,[z91,z0,z1,z7,z3,z4,z92]),(0,[z39,z0,z1,z93,z3,z4,z5]),(0,[z0,z1,z94,z7,z3,z4,z12])],[(0,[z95,z0,z1,z7,z3,z4,z5]),(0,[z96,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z97,z5]),(1,[z0,z1,z26,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z98,z12])],[(0,[z0,z1,z99,z100,z3,z4,z5]),(0,[z0,z1,z101,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z102,z16,z5]),(0,[z0,z1,z7,z3,z4,z103,z5]),(0,[z0,z1,z94,z7,z3,z4,z5])],[(0,[z0,z104,z1,z7,z3,z4,z5]),(0,[z105,z0,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z106,z5]),(0,[z107,z11,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z29,z4,z47]),(0,[z0,z1,z7,z3,z4,z108,z47])],[(0,[z0,z1,z109,z7,z3,z4,z5]),(0,[z110,z0,z1,z7,z3,z4,z5]),(0,[z0,z111,z1,z7,z3,z4,z5]),(0,[z112,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z93,z7,z3,z4,z47]),(0,[z0,z1,z113,z7,z3,z4,z114]),(0,[z115,z0,z1,z7,z3,z4,z5])],[(0,[z105,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z116,z4,z5]),(0,[z0,z1,z117,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z118,z4,z47])],[(0,[z0,z1,z7,z62,z3,z4,z12]),(0,[z0,z27,z7,z3,z4,z51,z5]),(0,[z0,z1,z119,z7,z3,z4,z5]),(1,[z0,z1,z113,z3,z4,z45]),(0,[z0,z1,z7,z3,z120,z4,z12]),(0,[z0,z121,z1,z7,z3,z4,z5])],[(0,[z0,z122,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z123,z5]),(0,[z0,z1,z7,z124,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z49]),(0,[z0,z1,z7,z3,z4,z125,z5]),(0,[z126,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z127,z3,z4,z5])]],
   [[(0,[z76,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z5,z128]),(1,[z0,z1,z7,z3,z4,z129])],[(0,[z130,z1,z100,z7,z3,z4,z5]),(0,[z91,z0,z1,z7,z3,z4,z131])],[(0,[z0,z1,z7,z132,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z98])],[(0,[z133,z0,z1,z7,z3,z4,z5]),(0,[z134,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z135,z5]),(0,[z0,z1,z58,z7,z3,z118,z5]),(0,[z0,z1,z136,z7,z3,z4,z5])],[(0,[z91,z1,z7,z3,z4,z5,z131]),(0,[z0,z1,z7,z137,z3,z4,z5]),(0,[z138,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z139,z7,z3,z4,z12])],[(0,[z76,z1,z7,z3,z140,z4,z5]),(0,[z0,z1,z7,z3,z141,z4,z5]),(0,[z0,z1,z7,z142,z3,z4,z5]),(1,[z0,z1,z83,z3,z4,z5]),(0,[z0,z65,z1,z7,z3,z102,z5]),(0,[z0,z1,z7,z3,z143,z4,z5]),(0,[z0,z1,z7,z3,z4,z144,z5]),(0,[z0,z1,z7,z3,z4,z145,z5])],[(0,[z130,z0,z1,z7,z3,z4,z47]),(0,[z80,z146,z1,z7,z3,z4,z5]),(0,[z0,z147,z1,z7,z3,z4,z5]),(0,[z0,z1,z148,z7,z3,z4,z5])],[(0,[z76,z0,z149,z7,z3,z4,z5]),(0,[z0,z1,z150,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z151,z4,z5]),(0,[z152,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z33,z4,z12])],[(0,[z153,z0,z154,z7,z3,z4,z5]),(0,[z153,z0,z1,z87,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z155]),(0,[z0,z1,z156,z7,z3,z4,z5]),(0,[z157,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z158,z3,z4,z5])],[(0,[z0,z1,z7,z159,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z160,z5]),(0,[z0,z1,z161,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z33,z4,z5]),(0,[z0,z65,z1,z7,z3,z162,z5]),(0,[z0,z1,z7,z3,z4,z51,z12]),(0,[z0,z1,z7,z3,z4,z163,z5])],[(0,[z0,z1,z7,z3,z4,z164,z5]),(0,[z105,z0,z1,z7,z3,z15,z5]),(0,[z8,z0,z1,z7,z3,z4,z47])],[(0,[z0,z1,z165,z7,z3,z4,z5]),(1,[z166,z0,z1,z7,z3,z4]),(0,[z39,z0,z32,z7,z3,z4,z5]),(0,[z0,z1,z7,z167,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z168,z5]),(1,[z0,z169,z7,z170,z4,z5]),(0,[z0,z169,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z5,z171]),(0,[z0,z1,z7,z3,z4,z51,z5]),(1,[z0,z1,z28,z3,z4,z5]),(0,[z0,z1,z7,z172,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z173])],[(0,[z0,z174,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z175,z5]),(0,[z176,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z37,z3,z4,z47]),(0,[z0,z1,z177,z3,z29,z4,z5]),(0,[z0,z1,z178,z7,z3,z4,z163]),(0,[z0,z1,z7,z3,z179,z4,z5])],[(0,[z80,z0,z1,z90,z3,z4,z5]),(0,[z0,z1,z180,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z15,z4,z47]),(0,[z0,z169,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z181,z4,z5]),(0,[z0,z1,z182,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z183,z4,z5]),(0,[z184,z0,z1,z7,z3,z4,z5])],[(0,[z130,z0,z1,z87,z3,z4,z5]),(0,[z8,z0,z7,z3,z33,z4,z5]),(0,[z0,z1,z7,z3,z4,z86,z12]),(0,[z0,z1,z7,z185,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z186,z4,z5]),(0,[z1,z149,z7,z3,z4,z5,z131]),(0,[z0,z65,z1,z7,z3,z4,z12]),(1,[z0,z1,z7,z3,z4,z187])],[(0,[z153,z0,z188,z7,z3,z4,z5]),(0,[z80,z0,z174,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z189,z5]),(0,[z0,z1,z7,z3,z190,z4,z5])],[(0,[z8,z191,z1,z7,z3,z4,z5]),(0,[z0,z65,z1,z7,z3,z4,z5]),(0,[z0,z1,z192,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z193])],[(0,[z0,z1,z7,z3,z4,z5,z194]),(0,[z0,z1,z100,z7,z3,z4,z47]),(0,[z80,z0,z1,z7,z3,z4,z12]),(0,[z0,z195,z1,z7,z3,z4,z5])],[(0,[z76,z32,z1,z7,z3,z4,z5]),(0,[z196,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z87,z3,z4,z5]),(0,[z0,z1,z7,z3,z197,z4,z5]),(0,[z0,z1,z198,z7,z3,z4,z5]),(0,[z50,z0,z7,z3,z4,z5,z86]),(0,[z0,z1,z7,z3,z4,z5,z199]),(0,[z0,z1,z58,z7,z3,z5,z59])],[(0,[z80,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z200,z5]),(0,[z0,z1,z7,z3,z201,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z86]),(0,[z0,z1,z7,z3,z4,z5,z202]),(0,[z0,z1,z7,z3,z78,z4,z47])],[(0,[z0,z188,z1,z7,z3,z4,z5])],[(0,[z0,z1,z203,z7,z3,z4,z5]),(0,[z0,z204,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z205])]],
   [[(0,[z0,z1,z7,z3,z206,z4,z5]),(0,[z0,z1,z207,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z12,z12])],[(0,[z146,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z49,z5]),(0,[z0,z1,z7,z170,z3,z4,z47]),(1,[z0,z1,z7,z3,z4,z47])],[(0,[z0,z1,z99,z7,z88,z4,z5]),(0,[z0,z1,z3,z88,z29,z4,z5]),(0,[z0,z1,z208,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z209,z4,z47])],[(0,[z0,z1,z7,z3,z4,z210,z5]),(0,[z76,z1,z7,z3,z4,z5,z131]),(0,[z211,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z212,z4,z5]),(0,[z0,z1,z177,z7,z3,z4,z12])],[(0,[z105,z1,z149,z7,z3,z4,z5]),(0,[z0,z213,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z214]),(1,[z0,z1,z7,z3,z215,z5]),(0,[z0,z1,z216,z7,z3,z4,z5]),(1,[z0,z1,z3,z183,z4,z5])],[(0,[z0,z1,z7,z3,z140,z4,z47]),(0,[z0,z1,z7,z3,z4,z217,z5]),(0,[z0,z1,z177,z7,z3,z4,z5]),(0,[z0,z1,z7,z218,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z12,z59]),(0,[z0,z1,z219,z7,z3,z4,z47])],[(0,[z220,z0,z1,z7,z3,z4,z5]),(0,[z221,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z222,z7,z3,z4,z5])],[(0,[z0,z1,z177,z37,z3,z4,z5]),(0,[z0,z1,z7,z3,z223,z4,z5]),(0,[z0,z1,z7,z3,z102,z4,z47]),(0,[z0,z1,z7,z3,z4,z5,z224])]],
   [[(0,[z80,z0,z1,z7,z3,z4,z225]),(1,[z191,z1,z7,z3,z4,z5]),(0,[z0,z1,z226,z7,z3,z4,z5]),(0,[z0,z1,z227,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z228,z4,z5])],[(0,[z0,z1,z7,z229,z3,z4,z5]),(0,[z0,z169,z7,z170,z3,z4,z5]),(0,[z0,z1,z230,z7,z3,z4,z5]),(0,[z0,z231,z1,z7,z3,z4,z5]),(0,[z232,z0,z1,z7,z3,z4,z5]),(0,[z233,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z234,z4,z5])],[(0,[z235,z0,z1,z7,z3,z4,z5])],[(0,[z0,z236,z1,z7,z3,z4,z47]),(0,[z0,z1,z178,z7,z3,z78,z5])],[(0,[z237,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z238,z3,z4,z5]),(1,[z0,z236,z37,z3,z4,z5]),(0,[z0,z1,z177,z93,z3,z4,z5]),(0,[z0,z1,z239,z7,z3,z29,z5])],[(0,[z0,z1,z240,z7,z3,z4,z5]),(1,[z0,z241,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z242,z5]),(0,[z0,z1,z7,z243,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z244]),(0,[z0,z1,z99,z7,z3,z4,z47]),(0,[z0,z1,z58,z7,z3,z4,z5])],[(0,[z245,z0,z1,z7,z3,z4,z5]),(0,[z166,z0,z1,z7,z3,z4,z5]),(0,[z246,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z247,z5]),(0,[z0,z1,z7,z3,z3,z4,z12])],[(0,[z0,z1,z7,z3,z4,z5,z63]),(0,[z0,z241,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z248,z5]),(0,[z0,z1,z249,z7,z3,z4,z12])]],
   [[(0,[z0,z1,z7,z3,z250,z4,z5]),(0,[z0,z1,z251,z3,z88,z4,z5]),(0,[z252,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z253,z3,z4,z47]),(0,[z0,z1,z58,z7,z3,z4,z59])],[(0,[z254,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z255,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z256]),(0,[z0,z1,z7,z3,z4,z257,z47])],[(0,[z0,z1,z7,z3,z4,z258,z5]),(0,[z0,z1,z7,z3,z215,z4,z5]),(0,[z0,z1,z7,z3,z4,z259,z5]),(0,[z0,z1,z178,z7,z3,z4,z12]),(0,[z0,z1,z7,z24,z3,z78,z5])],[(0,[z0,z1,z7,z3,z4,z260,z5]),(0,[z0,z1,z7,z192,z3,z4,z261]),(0,[z0,z1,z7,z3,z262,z4,z5])],[(0,[z0,z1,z7,z263,z3,z4,z5]),(0,[z0,z32,z1,z7,z3,z4,z47]),(0,[z0,z1,z264,z7,z3,z4,z5]),(0,[z91,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z131,z12]),(0,[z0,z1,z7,z3,z4,z265,z5]),(0,[z0,z1,z7,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z266,z4,z5]),(0,[z0,z1,z113,z7,z3,z4,z45]),(0,[z0,z1,z178,z7,z3,z4,z5])],[(0,[z0,z65,z32,z7,z3,z4,z5]),(0,[z0,z1,z249,z7,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z267,z5]),(0,[z0,z1,z23,z7,z3,z4,z5]),(0,[z268,z0,z1,z7,z3,z4,z5])],[(0,[z269,z0,z1,z7,z3,z4,z5]),(0,[z1,z149,z7,z3,z15,z4,z5]),(0,[z0,z1,z7,z270,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z175]),(0,[z0,z1,z7,z3,z271,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z272]),(0,[z0,z1,z273,z7,z3,z4,z5]),(0,[z0,z1,z274,z7,z3,z4,z47])],[(0,[z0,z1,z7,z3,z275,z4,z5])]],
   [[(0,[z32,z1,z149,z7,z3,z4,z5]),(0,[z276,z0,z1,z7,z3,z15,z5]),(0,[z0,z277,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z278]),(0,[z0,z1,z279,z7,z3,z4,z5]),(0,[z0,z1,z251,z7,z3,z30,z5])],[(0,[z0,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z113,z7,z3,z4,z47]),(0,[z0,z1,z7,z24,z3,z4,z12])],[(0,[z0,z1,z7,z3,z4,z5,z280]),(1,[z0,z1,z23,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z12])],[(0,[z0,z1,z7,z3,z4,z281,z5]),(0,[z0,z282,z1,z7,z3,z4,z5]),(1,[z8,z0,z7,z33,z4,z5]),(0,[z0,z169,z1,z7,z33,z4,z5]),(0,[z0,z1,z7,z24,z3,z4,z5])],[(0,[z0,z1,z283,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z5]),(0,[z0,z1,z7,z3,z284,z4,z5])],[(0,[z0,z1,z7,z3,z285,z4,z5]),(0,[z276,z0,z161,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z286,z4,z5])],[(0,[z0,z1,z7,z3,z287,z4,z5]),(0,[z288,z0,z1,z7,z3,z4,z5]),(0,[z80,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z289,z5]),(0,[z0,z1,z7,z3,z4,z290,z5]),(0,[z0,z1,z7,z3,z4,z47,z47])],[(1,[z0,z1,z7,z3,z43,z5]),(0,[z0,z1,z239,z3,z29,z4,z5]),(0,[z0,z1,z7,z3,z291,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z59])]],
   [[(0,[z0,z1,z7,z3,z4,z47,z292]),(0,[z0,z1,z7,z3,z4,z5,z293])],[(0,[z0,z1,z7,z3,z4,z294,z5]),(0,[z0,z1,z7,z3,z4,z5,z295]),(0,[z0,z1,z7,z192,z3,z4,z296]),(1,[z0,z1,z7,z3,z4,z19]),(0,[z0,z1,z7,z3,z4,z47,z145]),(0,[z0,z1,z297,z7,z3,z4,z5])],[(0,[z298,z0,z1,z7,z3,z4,z5]),(0,[z299,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z300,z3,z4,z5]),(1,[z107,z1,z7,z3,z4,z5]),(0,[z301,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z302,z4,z5])],[(0,[z0,z1,z7,z3,z4,z303,z5]),(0,[z0,z1,z7,z3,z304,z4,z5]),(0,[z0,z1,z305,z7,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z47]),(0,[z0,z1,z177,z3,z4,z5,z114])],[(0,[z306,z0,z1,z7,z3,z4,z5]),(0,[z0,z11,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z307,z4,z5]),(0,[z0,z1,z3,z4,z5,z308,z59])],[(0,[z1,z149,z7,z3,z140,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z309]),(0,[z310,z0,z1,z7,z3,z4,z5])],[(0,[z1,z7,z62,z3,z140,z4,z5]),(0,[z0,z1,z7,z3,z4,z311,z5]),(0,[z0,z1,z7,z312,z3,z4,z5]),(0,[z0,z1,z239,z7,z3,z78,z5])],[(0,[z0,z1,z7,z3,z4,z5,z225]),(0,[z0,z1,z7,z3,z4,z129,z5]),(0,[z0,z1,z313,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z123,z12]),(0,[z0,z1,z314,z7,z3,z4,z5]),(0,[z0,z1,z315,z7,z3,z4,z5]),(0,[z316,z0,z1,z7,z3,z4,z47])],[(0,[z1,z100,z7,z87,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z317,z5]),(0,[z0,z1,z249,z7,z3,z4,z318])],[(0,[z0,z27,z149,z7,z3,z4,z5]),(0,[z0,z93,z7,z37,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z4,z5])],[(0,[z319,z0,z1,z7,z3,z4,z12])],[(0,[z0,z320,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z321,z5]),(0,[z0,z1,z7,z3,z322,z4,z5]),(0,[z0,z1,z7,z3,z4,z129,z30]),(0,[z0,z1,z7,z3,z4,z47,z114])],[(0,[z0,z1,z323,z7,z3,z4,z5]),(0,[z319,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z47,z92]),(0,[z0,z1,z7,z192,z3,z4,z5]),(0,[z0,z1,z251,z3,z4,z30,z5]),(0,[z0,z1,z239,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z5,z308])],[(0,[z0,z1,z324,z7,z3,z4,z5]),(0,[z0,z1,z7,z325,z3,z4,z5]),(1,[z0,z65,z7,z3,z162,z5]),(0,[z0,z326,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z327,z3,z4,z5]),(0,[z0,z1,z249,z99,z3,z4,z5]),(0,[z0,z1,z113,z7,z3,z118,z4])],[(0,[z0,z1,z239,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z30,z12]),(0,[z0,z1,z58,z113,z7,z3,z4]),(0,[z0,z1,z94,z7,z4,z5,z12])]],
   [[(1,[z153,z1,z87,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z4,z5]),(0,[z0,z1,z7,z3,z328,z4,z5]),(0,[z50,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z239,z7,z3,z30,z5]),(0,[z0,z329,z1,z7,z3,z4,z5])],[(0,[z269,z0,z32,z7,z3,z4,z5]),(0,[z0,z1,z239,z37,z3,z4,z5]),(0,[z0,z169,z1,z7,z170,z4,z5]),(0,[z0,z1,z7,z3,z4,z30,z5]),(0,[z330,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z331,z5]),(0,[z0,z1,z7,z3,z4,z332,z5]),(0,[z0,z1,z333,z7,z3,z4,z5]),(0,[z0,z1,z251,z3,z4,z45,z5]),(0,[z0,z1,z7,z3,z4,z5,z334])],[(0,[z0,z1,z7,z3,z335,z4,z5])],[(0,[z0,z1,z7,z336,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z337,z5]),(0,[z0,z1,z7,z3,z338,z4,z5]),(0,[z0,z1,z7,z3,z339,z4,z5]),(0,[z39,z0,z236,z7,z3,z4,z5])],[(0,[z269,z1,z149,z7,z3,z4,z5]),(1,[z80,z1,z7,z140,z4,z5]),(0,[z91,z0,z340,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z341,z4,z5]),(0,[z0,z342,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z343,z4,z5]),(0,[z0,z1,z7,z3,z4,z16,z47])],[(0,[z0,z1,z149,z7,z3,z4,z12]),(0,[z153,z1,z7,z87,z3,z4,z5]),(0,[z0,z1,z344,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z47,z131]),(0,[z0,z1,z7,z3,z345,z4,z5]),(0,[z0,z1,z239,z93,z3,z4,z5]),(0,[z0,z7,z3,z102,z4,z162,z5]),(0,[z0,z1,z7,z346,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z347,z5]),(0,[z0,z1,z348,z7,z3,z4,z5]),(0,[z105,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z251,z7,z3,z29,z5]),(0,[z0,z1,z7,z3,z4,z349,z5]),(0,[z0,z1,z7,z3,z4,z350,z5])]],
   [[(0,[z0,z1,z149,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z351,z5]),(0,[z0,z352,z1,z7,z3,z4,z5]),(0,[z0,z1,z353,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z354,z4,z5])],[(0,[z355,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z356]),(1,[z91,z1,z7,z3,z4,z131])],[(0,[z0,z1,z154,z7,z3,z4,z5]),(0,[z0,z1,z7,z62,z3,z4,z47]),(0,[z0,z357,z1,z7,z3,z4,z5]),(0,[z358,z0,z1,z7,z3,z4,z5])],[(0,[z146,z1,z7,z62,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z359]),(1,[z0,z1,z3,z4,z5,z308])],[(1,[z269,z149,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z360,z4,z5]),(0,[z0,z1,z361,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z362,z5]),(0,[z0,z1,z363,z7,z3,z4,z5]),(0,[z0,z1,z7,z364,z3,z4,z5])],[(0,[z0,z365,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z87,z3,z4,z12]),(0,[z0,z1,z7,z366,z3,z4,z5]),(0,[z0,z1,z367,z7,z3,z4,z5]),(0,[z0,z1,z7,z368,z3,z4,z5]),(0,[z0,z369,z1,z7,z3,z4,z5]),(0,[z0,z1,z370,z7,z3,z4,z5]),(0,[z0,z1,z371,z7,z3,z4,z5])],[(0,[z0,z149,z7,z3,z102,z4,z5]),(0,[z0,z1,z7,z3,z4,z372,z5]),(0,[z0,z1,z7,z3,z4,z5,z373]),(0,[z0,z1,z374,z7,z3,z4,z5]),(0,[z375,z0,z1,z7,z3,z4,z5])],[(0,[z376,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z377,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z378]),(0,[z0,z1,z7,z170,z3,z4,z378])]],
   [[(0,[z0,z1,z7,z3,z4,z379,z5]),(0,[z0,z1,z7,z3,z4,z244,z5]),(0,[z0,z1,z7,z3,z4,z380,z5]),(0,[z0,z1,z7,z3,z4,z47,z381])],[(0,[z0,z1,z382,z7,z3,z4,z5]),(0,[z0,z1,z383,z7,z3,z4,z5]),(0,[z0,z1,z384,z7,z3,z4,z5]),(1,[z0,z1,z178,z7,z16,z5]),(0,[z0,z1,z178,z7,z3,z16,z5])],[(0,[z385,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z386,z4,z5])],[(0,[z0,z32,z7,z37,z3,z4,z5]),(0,[z46,z0,z1,z7,z3,z4,z5])],[(0,[z166,z0,z1,z149,z7,z3,z4]),(0,[z153,z130,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z52,z5]),(0,[z0,z1,z7,z3,z387,z4,z5]),(0,[z0,z1,z7,z388,z3,z4,z5]),(0,[z319,z50,z0,z1,z7,z3,z4]),(0,[z0,z389,z1,z7,z3,z4,z5]),(0,[z0,z390,z1,z7,z3,z4,z5])],[(0,[z0,z1,z391,z7,z3,z4,z5]),(0,[z392,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z393,z7,z3,z4,z5]),(0,[z0,z394,z1,z7,z3,z4,z5])],[(0,[z0,z1,z395,z7,z3,z4,z5]),(1,[z0,z1,z396,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z397])],[(0,[z0,z1,z398,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z399,z5]),(0,[z400,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z401,z7,z3,z4,z5]),(0,[z191,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z57])]],
   [[(0,[z402,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z403,z3,z4,z5]),(0,[z0,z1,z404,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z405,z4,z5]),(0,[z0,z1,z93,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z406,z5]),(0,[z407,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z408,z4,z5]),(0,[z0,z1,z7,z24,z3,z16,z5]),(0,[z0,z1,z7,z3,z4,z12,z409]),(0,[z0,z1,z410,z3,z4,z5,z59])],[(0,[z411,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z412,z3,z4,z5]),(0,[z413,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z414,z3,z4,z5])],[(0,[z76,z319,z1,z7,z3,z4,z5]),(0,[z415,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z416,z7,z3,z4,z5]),(0,[z0,z1,z28,z7,z3,z4,z5]),(0,[z235,z0,z1,z7,z3,z4,z12])],[(0,[z319,z1,z149,z7,z3,z4,z5]),(0,[z0,z417,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z418,z4,z5]),(0,[z0,z1,z7,z419,z3,z4,z5]),(0,[z0,z1,z420,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z421]),(0,[z0,z1,z178,z7,z24,z4,z5]),(0,[z0,z1,z7,z3,z4,z422,z47])],[(0,[z0,z1,z7,z3,z423,z4,z5]),(1,[z0,z154,z7,z3,z4,z5]),(0,[z0,z1,z424,z7,z3,z4,z5]),(0,[z319,z91,z1,z7,z3,z4,z5]),(0,[z0,z1,z425,z7,z3,z4,z5]),(1,[z0,z1,z66,z3,z4,z5]),(0,[z0,z1,z426,z7,z3,z4,z5]),(0,[z0,z1,z7,z427,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z428,z5])],[(0,[z0,z1,z7,z429,z3,z4,z5]),(0,[z0,z1,z7,z3,z29,z4,z5]),(0,[z0,z1,z7,z3,z4,z108,z5]),(0,[z0,z1,z58,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z118,z4,z12])],[(0,[z430,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z251,z3,z30,z5]),(0,[z431,z0,z1,z7,z3,z4,z12])]],
   [[(0,[z0,z1,z432,z7,z3,z4,z5]),(0,[z433,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z118,z4,z5])],[(0,[z153,z0,z1,z7,z3,z4,z12]),(0,[z0,z1,z251,z7,z3,z78,z5]),(0,[z431,z0,z1,z7,z3,z4,z5])],[(0,[z146,z0,z1,z7,z140,z4,z5]),(0,[z276,z1,z7,z3,z15,z4,z5]),(0,[z0,z1,z340,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z261]),(0,[z0,z1,z7,z3,z4,z5,z434]),(0,[z0,z435,z1,z7,z3,z4,z5])],[(0,[z76,z0,z1,z7,z3,z4,z5]),(0,[z153,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z436,z3,z4,z5]),(0,[z0,z437,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z118,z4,z59])],[(0,[z0,z1,z7,z3,z438,z4,z5]),(0,[z0,z1,z7,z3,z422,z5,z59])],[(0,[z0,z32,z7,z3,z102,z4,z5]),(1,[z0,z188,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z88,z4,z12]),(0,[z0,z1,z7,z3,z4,z439,z5]),(0,[z0,z1,z7,z3,z4,z5,z440])],[(0,[z0,z1,z7,z3,z4,z5,z441])],[(0,[z269,z0,z1,z7,z3,z4,z12]),(0,[z0,z1,z442,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z443,z5]),(0,[z130,z0,z1,z7,z3,z4,z12]),(1,[z0,z1,z7,z3,z4,z164]),(0,[z0,z1,z444,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z217,z47])]],
   [[(0,[z0,z1,z7,z3,z445,z4,z5]),(0,[z0,z1,z251,z7,z3,z4,z12]),(0,[z0,z1,z446,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z114,z12])],[(0,[z130,z0,z1,z7,z3,z4,z5]),(0,[z447,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z99,z87,z3,z4,z5]),(0,[z0,z448,z1,z7,z3,z4,z5]),(0,[z0,z11,z65,z7,z3,z4,z5]),(0,[z0,z1,z444,z7,z3,z4,z5])],[(0,[z0,z449,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z450,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z451]),(0,[z0,z1,z251,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z452]),(1,[z0,z1,z177,z3,z4,z114])],[(0,[z0,z1,z7,z3,z4,z5,z453])],[(0,[z0,z1,z7,z3,z454,z4,z5]),(0,[z276,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z455,z4,z5]),(0,[z0,z1,z99,z7,z192,z4,z5]),(0,[z0,z1,z113,z3,z4,z45,z5])],[(0,[z0,z1,z7,z3,z456,z4,z5]),(0,[z457,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z458,z4,z5]),(0,[z0,z1,z459,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z460,z5])],[(0,[z0,z1,z7,z7,z3,z4,z5]),(0,[z91,z0,z461,z7,z3,z4,z5]),(0,[z8,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z462,z7,z3,z4,z5]),(0,[z0,z1,z100,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z9,z5]),(0,[z463,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z37,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z296])],[(0,[z0,z1,z464,z7,z3,z4,z5]),(0,[z105,z276,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z465,z4,z5]),(0,[z0,z1,z466,z7,z3,z4,z5]),(0,[z0,z1,z7,z467,z3,z4,z5])],[(0,[z0,z320,z1,z149,z7,z3,z4]),(0,[z0,z1,z7,z3,z78,z123,z5]),(0,[z0,z468,z1,z7,z3,z4,z5]),(0,[z0,z1,z469,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z409]),(0,[z470,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z3,z4,z47])],[(0,[z0,z1,z7,z3,z4,z471,z5]),(0,[z0,z1,z7,z3,z4,z472,z5]),(0,[z0,z1,z249,z7,z3,z4,z47]),(0,[z473,z0,z1,z7,z3,z4,z5]),(0,[z0,z474,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z475,z5]),(0,[z0,z1,z476,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z477,z5])],[(0,[z0,z32,z27,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z478,z4,z5]),(1,[z0,z340,z7,z3,z4,z5]),(0,[z0,z1,z93,z3,z4,z30,z5]),(0,[z0,z1,z177,z7,z3,z4,z114]),(0,[z0,z1,z7,z3,z4,z5,z187]),(0,[z0,z1,z7,z3,z4,z479,z5])],[(0,[z0,z1,z7,z480,z3,z4,z5]),(0,[z0,z1,z481,z7,z3,z4,z5]),(0,[z0,z1,z482,z7,z3,z4,z5]),(0,[z0,z1,z7,z483,z3,z4,z5]),(0,[z484,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z178,z7,z3,z4,z47])],[(1,[z0,z11,z7,z3,z102,z5])]],
   [[(0,[z276,z0,z241,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z78,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z485])],[(0,[z0,z1,z7,z3,z4,z5,z486]),(0,[z0,z1,z7,z3,z487,z4,z5]),(0,[z0,z488,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z489,z5]),(0,[z0,z1,z7,z3,z4,z162,z12]),(0,[z0,z1,z7,z3,z4,z490,z5]),(0,[z0,z1,z7,z491,z3,z4,z5]),(1,[z0,z1,z7,z4,z47,z12])],[(0,[z492,z0,z1,z7,z3,z4,z5]),(0,[z0,z493,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z494,z4,z5]),(0,[z0,z1,z7,z3,z4,z495,z5]),(0,[z0,z1,z93,z3,z4,z45,z5]),(0,[z0,z1,z7,z3,z4,z496,z5]),(0,[z0,z1,z251,z239,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z497]),(0,[z0,z1,z7,z3,z4,z498,z12])],[(0,[z0,z1,z7,z3,z499,z4,z5]),(0,[z0,z1,z7,z3,z4,z162,z5]),(0,[z0,z1,z500,z7,z3,z4,z5]),(0,[z0,z1,z7,z501,z3,z4,z5])],[(1,[z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z502,z4,z5]),(0,[z0,z1,z7,z170,z3,z4,z5])],[(0,[z503,z0,z1,z7,z3,z4,z5]),(0,[z80,z0,z1,z7,z3,z43,z5]),(0,[z0,z1,z504,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z92,z5]),(0,[z0,z1,z7,z3,z4,z505,z5]),(0,[z506,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z209,z4,z5])],[(0,[z507,z0,z1,z7,z3,z4,z5]),(0,[z0,z508,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z509,z4,z5]),(0,[z39,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z192,z3,z4,z12])],[(0,[z0,z149,z7,z37,z3,z4,z5]),(0,[z0,z1,z7,z3,z510,z4,z5]),(0,[z0,z1,z511,z7,z3,z4,z5]),(0,[z0,z65,z1,z26,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z512,z5]),(0,[z0,z1,z249,z7,z3,z4,z244]),(0,[z0,z1,z7,z3,z4,z513,z5])]],
   [[(1,[z0,z1,z7,z3,z337,z5]),(0,[z0,z1,z7,z3,z140,z4,z5]),(0,[z0,z1,z7,z3,z4,z514,z5]),(0,[z0,z1,z219,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z498]),(0,[z0,z1,z7,z3,z4,z5,z292])],[(0,[z0,z1,z7,z515,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z516,z5]),(0,[z11,z326,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z517,z4,z5]),(0,[z0,z1,z7,z3,z102,z4,z5]),(0,[z0,z1,z7,z518,z3,z4,z5])],[(0,[z0,z1,z519,z7,z3,z4,z5])],[(0,[z0,z1,z520,z7,z3,z4,z5]),(0,[z233,z0,z1,z7,z3,z4,z5])],[(0,[z39,z0,z149,z7,z3,z4,z5]),(0,[z0,z1,z521,z7,z3,z4,z5]),(0,[z0,z1,z94,z7,z253,z4,z5])],[],[(1,[z0,z476,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z318]),(0,[z0,z1,z522,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z523,z5]),(0,[z0,z1,z7,z3,z4,z45,z12]),(0,[z0,z1,z524,z7,z3,z4,z5]),(0,[z0,z1,z94,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z5,z525])]],
   [[(0,[z0,z1,z7,z526,z3,z4,z5]),(0,[z0,z1,z7,z527,z3,z4,z5]),(0,[z0,z528,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z529]),(0,[z0,z1,z530,z7,z3,z4,z5]),(0,[z1,z7,z3,z15,z4,z123,z5]),(0,[z0,z1,z531,z7,z3,z4,z5]),(0,[z532,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z501,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z45,z5])],[(0,[z153,z0,z1,z100,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z533,z5]),(0,[z0,z1,z534,z7,z3,z4,z5]),(0,[z0,z1,z7,z253,z4,z47,z5]),(0,[z0,z535,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z536]),(0,[z537,z0,z1,z7,z3,z4,z5]),(0,[z319,z0,z27,z1,z7,z3,z4]),(0,[z8,z0,z1,z7,z3,z538,z5]),(0,[z0,z1,z7,z539,z3,z4,z5]),(0,[z0,z1,z7,z253,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z123,z47]),(1,[z276,z1,z7,z3,z15,z5]),(0,[z50,z0,z1,z7,z3,z4,z86]),(0,[z0,z1,z7,z3,z4,z5,z114])],[(0,[z0,z32,z1,z7,z3,z4,z12]),(0,[z540,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z541]),(0,[z91,z0,z1,z7,z3,z4,z12]),(0,[z0,z236,z7,z37,z3,z4,z5]),(1,[z39,z0,z93,z3,z4,z5]),(0,[z0,z1,z396,z7,z3,z4,z5])],[(0,[z276,z0,z1,z7,z3,z123,z5]),(0,[z8,z0,z1,z542,z3,z4,z5])],[(0,[z0,z32,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z2,z3,z4,z5]),(0,[z91,z0,z1,z7,z3,z4,z5]),(0,[z319,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z543,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z544,z3,z4,z5]),(0,[z130,z0,z1,z100,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z545]),(0,[z0,z1,z546,z7,z3,z4,z5]),(0,[z0,z547,z1,z7,z3,z4,z5])],[(0,[z319,z1,z7,z3,z4,z92,z5]),(0,[z0,z1,z542,z7,z3,z4,z5]),(0,[z50,z0,z27,z7,z3,z4,z5]),(0,[z0,z1,z274,z7,z3,z4,z5])],[(1,[z146,z1,z7,z62,z4,z5]),(0,[z31,z50,z1,z7,z3,z4,z5]),(1,[z50,z0,z7,z3,z4,z86]),(0,[z0,z1,z7,z3,z548,z4,z5]),(0,[z0,z1,z396,z7,z3,z4,z30]),(0,[z0,z1,z113,z7,z3,z4,z12])],[(0,[z8,z0,z1,z7,z33,z4,z5]),(0,[z0,z1,z7,z549,z3,z4,z5])],[(0,[z0,z1,z113,z7,z3,z4,z5])],[(0,[z0,z1,z66,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z550])],[(0,[z0,z1,z7,z3,z4,z551,z5]),(0,[z0,z1,z7,z3,z4,z5,z131]),(1,[z0,z1,z7,z3,z4,z125]),(0,[z0,z1,z7,z170,z3,z4,z125]),(0,[z0,z1,z178,z7,z3,z4,z19])],[(0,[z76,z269,z1,z7,z3,z4,z5]),(0,[z552,z0,z1,z7,z3,z4,z5]),(0,[z76,z146,z1,z7,z3,z4,z5]),(0,[z0,z1,z553,z7,z3,z4,z5]),(0,[z0,z554,z1,z7,z3,z4,z5]),(0,[z0,z1,z555,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z33,z4,z47]),(0,[z0,z1,z556,z7,z3,z4,z5]),(0,[z0,z1,z251,z7,z3,z16,z5]),(0,[z0,z1,z410,z7,z3,z4,z5])]],
   [[(0,[z557,z0,z1,z7,z3,z4,z5]),(0,[z558,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z249,z88,z4,z5]),(0,[z0,z1,z559,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z560,z4,z5])],[(0,[z0,z1,z7,z561,z3,z4,z5]),(0,[z0,z32,z169,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z562,z5]),(1,[z0,z1,z7,z3,z538,z5]),(0,[z0,z1,z7,z3,z162,z16,z5]),(0,[z563,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z564,z7,z3,z4,z5])],[(0,[z0,z1,z149,z7,z3,z4,z47]),(0,[z0,z565,z1,z7,z3,z4,z5]),(0,[z0,z1,z99,z192,z3,z4,z5]),(0,[z176,z0,z1,z7,z3,z4,z47])],[(0,[z0,z1,z7,z3,z566,z4,z5]),(0,[z0,z1,z7,z3,z567,z4,z5]),(0,[z0,z169,z1,z7,z3,z4,z47])],[(1,[z0,z1,z542,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z568,z5]),(0,[z0,z1,z7,z3,z4,z569,z5]),(0,[z0,z1,z7,z24,z3,z4,z75])],[(0,[z0,z1,z7,z3,z570,z4,z5]),(0,[z571,z0,z1,z7,z3,z4,z5]),(0,[z0,z7,z3,z4,z51,z5,z86])],[(1,[z0,z461,z7,z3,z4,z5]),(0,[z319,z0,z1,z7,z3,z4,z92]),(0,[z572,z0,z1,z7,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z573]),(0,[z0,z11,z1,z7,z3,z4,z5]),(0,[z0,z65,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z29,z4,z12]),(0,[z574,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z62,z3,z4,z164]),(0,[z0,z1,z93,z7,z3,z4,z12]),(0,[z0,z1,z58,z177,z7,z3,z4]),(1,[z0,z1,z7,z3,z4,z163]),(0,[z0,z1,z7,z3,z4,z5,z381]),(0,[z0,z1,z7,z3,z575,z4,z5])],[(0,[z0,z1,z7,z576,z3,z4,z5]),(0,[z0,z1,z7,z87,z3,z4,z47]),(0,[z146,z0,z1,z7,z62,z4,z5]),(0,[z577,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z578,z4,z5]),(0,[z316,z0,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z12,z485])],[(0,[z0,z169,z149,z7,z3,z4,z5]),(0,[z80,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z123,z16,z5]),(0,[z0,z1,z93,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z579,z5]),(0,[z0,z1,z7,z3,z4,z5,z580])],[(0,[z316,z0,z1,z7,z3,z4,z5])],[(0,[z76,z0,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z581,z5]),(0,[z0,z1,z7,z3,z582,z4,z5]),(1,[z0,z1,z7,z253,z4,z47]),(0,[z0,z1,z7,z3,z118,z422,z5])],[(0,[z583,z0,z1,z7,z3,z4,z5]),(0,[z0,z7,z170,z3,z33,z4,z5]),(0,[z0,z1,z584,z7,z3,z4,z5]),(0,[z0,z1,z177,z7,z3,z4,z45])],[(0,[z0,z65,z149,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z585,z5]),(0,[z91,z50,z0,z1,z7,z3,z4]),(0,[z0,z1,z7,z586,z3,z4,z5]),(0,[z587,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z24,z3,z183,z4,z5]),(1,[z0,z1,z7,z3,z118,z422])],[(0,[z80,z1,z7,z3,z140,z4,z5]),(0,[z588,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z589,z5]),(0,[z319,z0,z1,z7,z3,z4,z131]),(0,[z0,z1,z7,z590,z3,z4,z5]),(0,[z0,z591,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z592,z7,z3,z4,z5])],[(0,[z0,z1,z7,z593,z3,z4,z5]),(0,[z8,z0,z1,z7,z170,z4,z5]),(0,[z50,z0,z1,z7,z3,z4,z12]),(0,[z594,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z595,z5])],[(0,[z0,z596,z1,z7,z3,z4,z5]),(0,[z0,z1,z177,z7,z3,z4,z47])],[(1,[z0,z1,z7,z3,z9,z5]),(0,[z0,z1,z7,z597,z3,z4,z5]),(0,[z50,z0,z1,z7,z3,z4,z5]),(0,[z0,z27,z1,z501,z3,z4,z5]),(0,[z0,z1,z72,z7,z3,z4,z5]),(0,[z598,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z599,z5]),(0,[z105,z0,z1,z7,z3,z123,z5]),(0,[z0,z1,z7,z3,z4,z600,z5]),(1,[z0,z1,z239,z3,z29,z5]),(0,[z0,z1,z58,z7,z3,z4,z422]),(0,[z0,z1,z7,z3,z118,z4,z422]),(0,[z0,z1,z7,z601,z3,z4,z5])],[(0,[z602,z0,z1,z7,z3,z4,z5]),(0,[z0,z603,z1,z7,z3,z4,z5]),(0,[z0,z1,z604,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z45,z5,z114]),(0,[z0,z1,z7,z605,z3,z4,z5]),(0,[z0,z1,z227,z7,z3,z4,z47])],[(0,[z0,z1,z7,z606,z3,z4,z5]),(0,[z607,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z78,z102,z5]),(0,[z0,z1,z7,z3,z608,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z609]),(0,[z0,z1,z7,z3,z4,z16,z12]),(0,[z0,z1,z7,z3,z4,z610,z5])],[(0,[z8,z0,z1,z7,z3,z4,z12]),(1,[z231,z1,z7,z3,z4,z5]),(0,[z0,z1,z239,z7,z3,z16,z5]),(0,[z0,z1,z611,z7,z3,z4,z5]),(0,[z0,z1,z612,z7,z3,z4,z5]),(0,[z0,z613,z1,z7,z3,z4,z5])]],
   [[(1,[z0,z320,z1,z7,z3,z4]),(0,[z80,z0,z1,z7,z140,z4,z5]),(0,[z8,z277,z1,z7,z3,z4,z5]),(0,[z31,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z16,z5]),(0,[z463,z0,z1,z7,z3,z4,z12])],[(0,[z614,z0,z1,z7,z3,z4,z5]),(0,[z615,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z37,z3,z4,z12])],[(1,[z0,z1,z7,z3,z4,z63]),(0,[z0,z1,z7,z3,z15,z4,z12]),(0,[z0,z1,z7,z3,z538,z4,z5]),(0,[z0,z1,z7,z3,z616,z4,z5]),(0,[z0,z1,z7,z3,z4,z12,z529]),(0,[z0,z1,z58,z7,z3,z4,z47])],[(0,[z617,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z78,z162,z5]),(0,[z0,z1,z618,z7,z3,z4,z5]),(0,[z0,z1,z619,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z15,z4,z5]),(0,[z0,z1,z620,z7,z3,z4,z5]),(0,[z0,z1,z178,z7,z4,z16,z5]),(0,[z0,z1,z621,z7,z3,z4,z5])],[(0,[z153,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z62,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z622,z5]),(0,[z0,z1,z623,z7,z3,z4,z5]),(0,[z0,z1,z251,z177,z3,z4,z5]),(0,[z0,z1,z7,z3,z624,z4,z5]),(0,[z0,z1,z7,z3,z120,z4,z5])],[(0,[z625,z0,z1,z7,z3,z4,z5]),(0,[z626,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z627,z7,z3,z4,z5])],[(0,[z628,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z629]),(0,[z0,z1,z100,z7,z3,z4,z12]),(0,[z80,z0,z1,z7,z3,z4,z175]),(0,[z0,z1,z7,z630,z3,z4,z5]),(0,[z0,z1,z7,z24,z3,z4,z187]),(0,[z0,z1,z7,z3,z4,z580,z12])]],
   [[(1,[z0,z1,z90,z3,z4,z5]),(0,[z0,z11,z7,z3,z102,z4,z5]),(0,[z0,z1,z631,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z296,z5])],[(0,[z0,z1,z632,z7,z3,z4,z5]),(0,[z0,z1,z100,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z633,z4,z5]),(0,[z0,z1,z7,z3,z88,z4,z47]),(0,[z0,z1,z7,z3,z78,z4,z12])],[(0,[z0,z634,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z635,z3,z4,z5])],[(0,[z269,z0,z1,z7,z3,z4,z47]),(0,[z0,z636,z1,z7,z3,z4,z5]),(1,[z0,z174,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z92,z5,z131]),(0,[z8,z0,z169,z7,z3,z4,z5]),(0,[z0,z1,z99,z3,z29,z4,z5]),(0,[z0,z1,z139,z7,z3,z4,z5])],[(0,[z0,z1,z7,z637,z3,z4,z5]),(0,[z0,z1,z7,z638,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z378]),(0,[z0,z1,z7,z192,z3,z135,z5]),(0,[z0,z1,z251,z7,z3,z4,z47]),(0,[z0,z1,z177,z113,z3,z4,z5]),(0,[z0,z1,z7,z639,z3,z4,z5])],[(1,[z76,z32,z7,z3,z4,z5]),(0,[z146,z0,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z170,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z47,z86]),(0,[z0,z1,z640,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z12])],[(0,[z0,z1,z7,z3,z4,z92,z12]),(1,[z277,z1,z7,z3,z4,z5]),(1,[z0,z1,z410,z3,z4,z5])],[(0,[z146,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z135,z5]),(0,[z0,z1,z641,z7,z3,z4,z5]),(0,[z0,z1,z177,z7,z3,z118,z4]),(0,[z0,z642,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z5,z643]),(0,[z0,z1,z644,z7,z3,z4,z5]),(1,[z0,z1,z99,z192,z4,z5]),(0,[z0,z1,z7,z24,z3,z4,z47]),(0,[z0,z645,z1,z7,z3,z4,z5])],[(0,[z76,z0,z32,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z140,z4,z12]),(0,[z0,z1,z7,z3,z4,z5,z646]),(0,[z0,z1,z647,z7,z3,z4,z5]),(0,[z648,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z649,z7,z3,z4,z5])],[(0,[z269,z0,z149,z7,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z86]),(0,[z0,z1,z249,z7,z192,z4,z5]),(1,[z0,z1,z94,z7,z4,z12])],[(0,[z0,z1,z650,z7,z3,z4,z5]),(0,[z105,z1,z7,z3,z4,z123,z5]),(0,[z0,z1,z7,z3,z102,z4,z12]),(0,[z0,z1,z7,z3,z4,z75,z5])],[(0,[z0,z1,z7,z3,z4,z651,z5]),(0,[z0,z1,z7,z78,z4,z16,z5])],[(0,[z0,z1,z7,z3,z4,z652,z5]),(0,[z0,z1,z653,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z654,z5]),(0,[z655,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z656]),(0,[z0,z657,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z658,z4,z5]),(0,[z0,z1,z7,z3,z4,z659,z5]),(0,[z0,z1,z7,z3,z4,z422,z12])],[(0,[z660,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z661]),(0,[z0,z1,z7,z24,z78,z4,z5]),(0,[z0,z1,z7,z3,z4,z12,z10])],[(0,[z0,z236,z1,z7,z3,z4,z12]),(0,[z0,z1,z662,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z422,z5])]],
   [[(0,[z663,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z664,z3,z4,z5]),(0,[z0,z1,z665,z7,z3,z4,z5])],[(0,[z0,z1,z7,z666,z3,z4,z5]),(0,[z0,z1,z7,z3,z78,z15,z5]),(0,[z0,z236,z1,z7,z3,z4,z5]),(0,[z0,z1,z37,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z667,z5]),(0,[z0,z1,z7,z3,z4,z668,z5]),(0,[z0,z1,z99,z7,z3,z4,z12])],[(1,[z0,z1,z7,z3,z4,z225]),(0,[z0,z1,z669,z7,z3,z4,z5]),(0,[z0,z1,z251,z99,z3,z4,z5])],[(0,[z670,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z671,z7,z3,z4,z5]),(0,[z0,z236,z1,z37,z3,z4,z5]),(0,[z0,z1,z99,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z173,z12]),(0,[z0,z1,z7,z253,z3,z4,z12])],[(0,[z0,z1,z99,z37,z3,z4,z5]),(0,[z0,z1,z672,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z162,z47]),(0,[z0,z1,z673,z7,z3,z4,z5])],[(0,[z0,z149,z7,z3,z33,z4,z5]),(0,[z80,z0,z1,z7,z3,z337,z5]),(1,[z105,z1,z7,z3,z123,z5])],[(0,[z0,z1,z7,z674,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z257,z5]),(0,[z0,z1,z675,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z261])]],
   [[(0,[z0,z1,z676,z7,z3,z4,z5]),(0,[z0,z236,z1,z93,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z677,z5])],[(0,[z0,z461,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z678,z4,z5]),(0,[z0,z679,z1,z7,z3,z4,z5])],[(1,[z0,z161,z7,z3,z4,z5]),(0,[z0,z1,z99,z93,z3,z4,z5]),(0,[z0,z1,z7,z3,z680,z4,z5]),(0,[z681,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z192,z3,z4,z47]),(0,[z0,z1,z7,z682,z3,z4,z5])],[(0,[z683,z0,z1,z7,z3,z4,z5])],[(1,[z319,z1,z7,z3,z4,z92]),(1,[z326,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z684,z3,z4,z5]),(0,[z0,z1,z239,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z685,z5])],[(0,[z80,z0,z476,z7,z3,z4,z5]),(0,[z276,z0,z1,z7,z3,z4,z12]),(0,[z0,z11,z1,z7,z3,z102,z5]),(0,[z0,z1,z7,z192,z3,z215,z5])],[(0,[z0,z1,z7,z3,z4,z30,z47])],[(1,[z130,z1,z100,z3,z4,z5]),(0,[z0,z1,z7,z3,z686,z4,z5]),(0,[z276,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z687,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z47,z51]),(1,[z0,z1,z7,z3,z4,z318]),(0,[z0,z1,z249,z3,z88,z4,z5]),(0,[z0,z688,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z47,z685])]],
   [[(0,[z689,z0,z1,z7,z3,z4,z5]),(0,[z690,z0,z1,z7,z3,z4,z5]),(0,[z105,z76,z1,z7,z3,z4,z5]),(0,[z691,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z692,z7,z3,z4,z5]),(0,[z0,z1,z693,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z694,z4,z5])],[(0,[z0,z149,z7,z3,z4,z5,z86]),(0,[z0,z695,z1,z7,z3,z4,z5]),(0,[z0,z65,z7,z3,z4,z162,z5]),(0,[z0,z1,z7,z3,z696,z4,z5]),(0,[z0,z1,z7,z697,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z698,z5])],[(0,[z0,z11,z1,z7,z3,z162,z5]),(0,[z0,z1,z7,z3,z4,z47,z12]),(0,[z0,z1,z7,z3,z4,z699,z5])],[(0,[z0,z1,z7,z3,z4,z45,z47]),(0,[z0,z1,z7,z4,z47,z5,z12]),(0,[z700,z0,z1,z7,z3,z4,z5])],[(0,[z701,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z702,z7,z3,z4,z5]),(0,[z8,z0,z1,z7,z3,z4,z57]),(0,[z703,z0,z1,z7,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z51]),(0,[z0,z1,z7,z3,z4,z47,z5]),(0,[z0,z535,z1,z7,z3,z4,z47])],[(0,[z0,z1,z7,z3,z3,z4,z5]),(0,[z91,z0,z27,z1,z7,z3,z4]),(0,[z704,z0,z1,z7,z3,z4,z5])],[(0,[z146,z1,z149,z7,z3,z4,z5]),(0,[z50,z231,z1,z7,z3,z4,z5]),(0,[z0,z1,z249,z7,z3,z4,z5])],[(0,[z705,z0,z1,z7,z3,z4,z5]),(0,[z39,z0,z93,z7,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z12]),(0,[z0,z706,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z47,z59])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z462,z88,z4,z5]),(0,[z0,z174,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z707,z5]),(0,[z0,z1,z7,z3,z4,z708]),(0,[z709,z1,z7,z3,z4,z47])],[(0,[z0,z122,z37,z3,z4,z5])],[(0,[z76,z32,z7,z3,z4,z12]),(0,[z176,z1,z7,z3,z4,z145])],[(0,[z0,z1,z710,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z711]),(0,[z277,z1,z7,z3,z4,z12]),(0,[z0,z1,z410,z3,z4,z12])],[(0,[z166,z0,z340,z7,z3,z4]),(0,[z0,z712,z7,z3,z4,z5])],[(0,[z0,z93,z713,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z714]),(0,[z0,z1,z99,z192,z4,z12]),(0,[z0,z1,z410,z3,z4,z5]),(0,[z715,z1,z7,z3,z4,z12])],[(0,[z492,z149,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z716]),(0,[z0,z1,z7,z3,z4,z717]),(0,[z0,z1,z28,z3,z4,z12])],[(0,[z0,z1,z3,z4,z5,z718]),(0,[z0,z1,z7,z3,z4,z719]),(0,[z715,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z28,z3,z4,z5]),(0,[z0,z169,z7,z170,z4,z5]),(0,[z0,z1,z7,z3,z4,z720]),(0,[z0,z1,z251,z396,z3,z30]),(0,[z0,z1,z721,z3,z4,z47]),(0,[z0,z1,z7,z601,z4,z47])],[(0,[z0,z1,z722,z7,z3,z5]),(0,[z723,z1,z7,z3,z4,z5]),(0,[z0,z724,z1,z7,z3,z4]),(0,[z0,z1,z7,z590,z4,z47])],[(1,[z0,z1,z725,z4,z5]),(0,[z0,z1,z178,z7,z16,z19]),(0,[z0,z1,z274,z3,z4,z217])],[(0,[z0,z1,z726,z3,z4,z5]),(0,[z0,z1,z7,z3,z538,z57]),(0,[z0,z1,z7,z3,z4,z727]),(0,[z728,z1,z7,z3,z4,z5]),(0,[z0,z1,z99,z725,z4,z5]),(0,[z0,z1,z444,z7,z3,z485])],[(0,[z0,z1,z7,z3,z729,z5]),(0,[z0,z1,z7,z3,z4,z730]),(0,[z0,z1,z7,z3,z4,z731]),(0,[z0,z1,z7,z539,z4,z12]),(0,[z0,z1,z7,z3,z4,z187])],[],[(0,[z105,z1,z7,z3,z303,z5]),(0,[z0,z340,z7,z3,z4,z47]),(0,[z319,z1,z7,z3,z4,z498]),(0,[z732,z1,z7,z3,z4,z5]),(0,[z0,z1,z733,z3,z4,z47])],[(0,[z0,z1,z7,z3,z734,z5]),(0,[z0,z1,z7,z3,z4,z735]),(0,[z0,z1,z7,z3,z736,z5]),(0,[z0,z1,z7,z3,z4,z737]),(0,[z0,z1,z713,z3,z4,z5]),(0,[z277,z169,z7,z3,z4,z5]),(1,[z0,z7,z738,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z739]),(0,[z1,z7,z740,z3,z4,z5]),(0,[z0,z11,z7,z3,z102,z47]),(0,[z0,z1,z7,z3,z4,z741]),(0,[z742,z1,z7,z3,z4,z12])],[(0,[z1,z7,z3,z4,z743,z5]),(0,[z91,z231,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z744]),(0,[z0,z688,z93,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z745]),(0,[z0,z746,z7,z3,z4,z5]),(0,[z0,z1,z3,z88,z215,z5])],[(0,[z0,z1,z7,z747,z4,z5]),(0,[z0,z1,z542,z3,z9,z5]),(0,[z0,z1,z7,z3,z4,z748]),(0,[z0,z1,z251,z396,z3,z4]),(0,[z0,z1,z7,z4,z290,z12]),(1,[z0,z1,z3,z4,z749]),(0,[z0,z1,z7,z4,z47,z750]),(0,[z0,z1,z7,z3,z4,z751])],[(0,[z105,z1,z7,z3,z123,z12]),(0,[z0,z1,z7,z3,z4,z752]),(0,[z11,z326,z7,z3,z102,z5]),(0,[z0,z1,z7,z3,z753,z5]),(0,[z0,z1,z113,z3,z4,z699])],[],[(0,[z0,z754,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z755,z5]),(0,[z0,z1,z756,z3,z4,z5]),(0,[z0,z1,z491,z88,z4,z5]),(0,[z0,z1,z757,z7,z3,z12])],[(0,[z0,z1,z7,z3,z4,z758]),(0,[z0,z1,z7,z3,z759,z5]),(0,[z0,z1,z760,z3,z4,z5]),(0,[z0,z1,z761,z3,z4,z5]),(0,[z0,z1,z274,z3,z4,z45])],[(0,[z0,z1,z7,z3,z762,z5]),(0,[z1,z7,z62,z763,z4,z5]),(0,[z0,z161,z7,z3,z4,z12])]],
   [[(0,[z1,z100,z740,z3,z4,z5]),(0,[z0,z1,z7,z764,z4,z5]),(0,[z0,z1,z7,z3,z4,z765]),(0,[z277,z7,z3,z33,z4,z5]),(0,[z0,z1,z7,z3,z538,z49])],[(0,[z0,z161,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z337,z47]),(0,[z0,z1,z3,z766,z4,z5]),(0,[z0,z1,z7,z368,z4,z47]),(0,[z0,z767,z7,z3,z4,z5]),(0,[z463,z1,z7,z3,z4,z529]),(0,[z0,z768,z7,z3,z4,z5])],[(0,[z0,z1,z769,z3,z4,z5]),(0,[z0,z65,z7,z3,z162,z47]),(0,[z0,z1,z7,z3,z4,z770])],[(0,[z0,z1,z7,z3,z4,z771]),(0,[z0,z772,z7,z3,z4,z5]),(0,[z319,z1,z7,z3,z4,z92]),(0,[z0,z1,z391,z7,z4,z12]),(0,[z0,z1,z531,z3,z30,z5]),(0,[z0,z1,z7,z3,z4,z773]),(0,[z0,z1,z3,z4,z774,z12]),(0,[z0,z1,z7,z575,z4,z47])],[(0,[z191,z1,z7,z3,z4,z5]),(0,[z130,z1,z100,z3,z4,z12]),(0,[z0,z1,z7,z3,z775,z5]),(0,[z0,z1,z3,z4,z45,z452])],[],[(0,[z130,z1,z100,z3,z4,z5]),(0,[z0,z1,z83,z3,z538,z5]),(0,[z0,z1,z7,z3,z4,z318])],[(0,[z0,z1,z7,z3,z4,z776]),(0,[z0,z1,z7,z3,z777,z5]),(0,[z0,z1,z778,z3,z4,z5]),(0,[z779,z1,z7,z3,z4,z5])]],
   [[(0,[z76,z695,z7,z3,z4,z5]),(0,[z0,z476,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z780]),(0,[z0,z1,z7,z3,z781,z5]),(0,[z0,z782,z7,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z774])],[(0,[z0,z1,z7,z3,z4,z783]),(0,[z0,z784,z7,z3,z4,z5]),(0,[z0,z169,z7,z170,z4,z125]),(0,[z0,z1,z501,z3,z4,z47]),(0,[z0,z1,z785,z3,z4,z47])],[(0,[z0,z786,z7,z3,z4,z5]),(0,[z105,z1,z7,z3,z787,z5]),(0,[z0,z1,z788,z7,z3,z4]),(0,[z431,z0,z7,z3,z4,z10])],[(0,[z0,z1,z7,z3,z4,z789]),(0,[z0,z1,z7,z3,z790,z5])],[(0,[z0,z1,z791,z3,z4,z5]),(0,[z276,z1,z7,z3,z15,z47]),(0,[z1,z7,z3,z4,z92,z743]),(0,[z792,z0,z1,z7,z3,z4]),(0,[z0,z1,z793,z3,z4,z5]),(0,[z0,z1,z58,z410,z3,z59])],[(0,[z0,z1,z7,z3,z794,z5]),(0,[z0,z1,z7,z3,z4,z795]),(0,[z463,z1,z7,z3,z4,z131]),(0,[z0,z27,z377,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z796]),(0,[z39,z0,z93,z3,z4,z47]),(0,[z0,z797,z7,z3,z4,z5])],[(0,[z798,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z799])]],
   [[(0,[z0,z1,z7,z3,z4,z800]),(0,[z0,z1,z7,z339,z4,z12])],[(0,[z0,z149,z501,z3,z4,z5]),(0,[z0,z1,z7,z3,z801,z5])],[(0,[z802,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z803]),(0,[z0,z1,z7,z3,z804,z5]),(0,[z0,z1,z7,z3,z805,z5])],[(0,[z0,z1,z806,z3,z4,z5]),(0,[z0,z807,z7,z3,z4,z5]),(0,[z80,z1,z7,z763,z4,z5]),(0,[z146,z1,z7,z62,z4,z47])],[(0,[z0,z1,z90,z3,z43,z5])],[(0,[z153,z188,z87,z3,z4,z5]),(0,[z0,z1,z808,z7,z3,z4]),(0,[z0,z169,z7,z738,z4,z5])],[(0,[z0,z1,z7,z3,z337,z175]),(0,[z809,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z810]),(0,[z0,z1,z7,z3,z4,z811]),(0,[z0,z174,z7,z3,z43,z5]),(0,[z0,z1,z239,z3,z569,z5])]],
   [[(0,[z0,z1,z7,z812,z4,z5]),(0,[z277,z1,z7,z3,z4,z57]),(0,[z0,z1,z7,z3,z4,z813])],[(0,[z0,z1,z814,z3,z4,z5]),(0,[z0,z815,z7,z3,z4,z5]),(0,[z276,z241,z7,z3,z15,z5]),(0,[z0,z1,z7,z3,z4,z57]),(0,[z107,z11,z7,z3,z102,z5]),(0,[z0,z1,z3,z816,z4,z5]),(0,[z0,z1,z58,z7,z3,z59]),(0,[z0,z1,z58,z410,z3,z4])],[(0,[z0,z1,z7,z3,z817,z4]),(0,[z0,z1,z7,z3,z538,z47])],[(0,[z0,z1,z7,z3,z43,z5]),(0,[z818,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z597,z4,z12]),(1,[z0,z1,z7,z4,z750])],[(0,[z0,z1,z7,z3,z4,z75])],[(0,[z0,z819,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z820]),(0,[z0,z476,z7,z3,z4,z175]),(0,[z0,z1,z821,z3,z4,z5]),(0,[z0,z1,z822,z7,z3,z5]),(0,[z0,z1,z823,z3,z4,z5]),(0,[z0,z1,z3,z824,z30,z5]),(0,[z0,z1,z139,z3,z4,z114]),(0,[z235,z1,z7,z3,z4,z498])],[(0,[z107,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z825,z3,z5]),(0,[z80,z1,z7,z140,z4,z175]),(0,[z0,z1,z26,z3,z4,z12]),(0,[z0,z1,z7,z826,z4,z5]),(0,[z0,z1,z7,z3,z118,z173])],[(0,[z0,z1,z7,z827,z4,z5]),(0,[z0,z461,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z828]),(0,[z0,z829,z7,z3,z4,z47])]],
   [[(0,[z0,z1,z7,z387,z4,z12]),(0,[z91,z1,z7,z3,z4,z145]),(0,[z0,z1,z26,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z830])],[(0,[z146,z1,z7,z763,z4,z5]),(0,[z0,z528,z37,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z831])],[(0,[z0,z1,z832,z3,z4,z5]),(0,[z0,z1,z99,z336,z4,z5]),(0,[z0,z1,z7,z3,z5,z833]),(0,[z0,z1,z249,z88,z4,z318]),(0,[z0,z1,z7,z172,z4,z47])],[(0,[z0,z1,z7,z3,z834,z5]),(0,[z0,z1,z251,z3,z30,z47]),(0,[z0,z1,z7,z539,z16,z5]),(0,[z0,z1,z835,z3,z4,z12])],[(0,[z0,z1,z7,z3,z4,z836]),(0,[z191,z1,z542,z3,z4,z5]),(0,[z0,z1,z7,z3,z837,z5]),(0,[z233,z1,z7,z3,z4,z52])],[(0,[z0,z1,z7,z3,z838,z5]),(0,[z0,z1,z7,z3,z4,z839]),(0,[z0,z840,z7,z3,z4,z5]),(0,[z277,z1,z7,z3,z4,z49]),(0,[z1,z7,z3,z4,z841,z5]),(0,[z0,z1,z113,z3,z4,z45])],[(0,[z0,z1,z7,z3,z842,z5]),(0,[z0,z1,z7,z3,z843,z5]),(0,[z0,z476,z7,z3,z43,z5]),(0,[z0,z1,z7,z3,z43,z225]),(0,[z0,z1,z7,z3,z4,z49]),(0,[z0,z1,z251,z3,z698,z5]),(0,[z0,z7,z3,z4,z844,z12]),(0,[z0,z1,z219,z7,z3,z381])],[(0,[z1,z7,z3,z763,z4,z5]),(0,[z0,z1,z845,z7,z3,z4])]],
   [[(0,[z0,z1,z7,z4,z47,z74]),(0,[z0,z1,z7,z3,z135,z12])],[(0,[z0,z1,z177,z3,z4,z749]),(0,[z0,z1,z846,z3,z4,z5])],[(0,[z0,z1,z83,z3,z4,z12]),(0,[z0,z1,z847,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z848]),(0,[z0,z1,z7,z3,z4,z849]),(0,[z0,z1,z3,z4,z47,z308])],[(0,[z0,z1,z7,z142,z4,z12]),(0,[z277,z1,z83,z3,z4,z5]),(0,[z0,z1,z99,z192,z135,z5]),(0,[z0,z1,z7,z3,z4,z850])],[(0,[z166,z231,z1,z7,z3,z4]),(0,[z153,z1,z87,z3,z4,z5]),(0,[z0,z1,z83,z3,z4,z5]),(0,[z0,z1,z851,z7,z3,z4]),(0,[z0,z1,z852,z3,z4,z5]),(0,[z0,z1,z7,z3,z833,z12])],[(0,[z0,z1,z239,z3,z29,z47]),(0,[z0,z1,z7,z3,z209,z108])],[(0,[z91,z340,z7,z3,z4,z131]),(0,[z0,z1,z7,z3,z4,z853]),(0,[z0,z329,z7,z3,z102,z5])],[(0,[z0,z1,z7,z3,z854,z5]),(0,[z276,z1,z7,z3,z787,z5]),(0,[z0,z1,z725,z88,z4,z5])]],
   [[(0,[z0,z1,z7,z763,z4,z5]),(0,[z0,z1,z3,z4,z5,z855]),(0,[z231,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z4,z661,z12])],[(0,[z0,z1,z856,z3,z4,z5]),(0,[z0,z1,z857,z3,z4,z5]),(0,[z0,z169,z7,z170,z4,z12]),(0,[z0,z858,z7,z3,z4,z12])],[(0,[z0,z169,z7,z666,z4,z5]),(0,[z0,z859,z7,z3,z4,z5]),(0,[z0,z1,z860,z3,z4,z5]),(0,[z0,z1,z7,z124,z78,z5]),(0,[z0,z1,z692,z3,z4,z45]),(0,[z0,z1,z251,z3,z36,z5])],[(0,[z166,z0,z1,z7,z3,z4]),(0,[z0,z1,z861,z3,z4,z5]),(0,[z0,z1,z7,z229,z4,z12]),(0,[z0,z1,z7,z3,z862,z5]),(0,[z191,z1,z7,z3,z9,z5]),(0,[z0,z1,z7,z3,z118,z568]),(0,[z0,z858,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z863,z5]),(0,[z0,z1,z177,z3,z4,z451]),(0,[z8,z0,z7,z33,z538,z5]),(0,[z864,z1,z7,z3,z4,z5])],[(0,[z80,z1,z7,z140,z337,z5]),(0,[z91,z1,z7,z3,z4,z131])],[(0,[z0,z1,z865,z3,z4,z5]),(0,[z385,z32,z7,z3,z4,z5]),(0,[z0,z866,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z5,z867]),(0,[z0,z1,z868,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z869]),(0,[z0,z1,z7,z3,z215,z296])]],
   [[(0,[z269,z149,z7,z3,z4,z5])],[(0,[z0,z1,z7,z456,z4,z12]),(0,[z0,z1,z90,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z870]),(0,[z0,z871,z7,z3,z4,z5]),(0,[z233,z1,z7,z3,z4,z92]),(0,[z0,z1,z542,z3,z4,z57]),(0,[z0,z1,z396,z3,z29,z4])],[(0,[z0,z1,z7,z3,z4,z872]),(0,[z39,z0,z632,z3,z4,z5]),(0,[z0,z1,z873,z3,z4,z5]),(0,[z874,z1,z7,z3,z4,z5]),(0,[z0,z7,z738,z33,z4,z5]),(0,[z0,z1,z58,z3,z308,z59])],[(0,[z0,z32,z26,z3,z4,z5]),(0,[z0,z1,z7,z682,z78,z5])],[(0,[z0,z1,z875,z3,z4,z5]),(0,[z0,z1,z876,z7,z3,z4]),(0,[z80,z476,z7,z140,z4,z5]),(0,[z0,z174,z7,z3,z4,z47]),(0,[z0,z1,z2,z3,z43,z5]),(0,[z0,z7,z3,z738,z4,z5]),(0,[z0,z877,z7,z3,z4,z5])],[(0,[z0,z1,z58,z7,z3,z36]),(0,[z0,z1,z178,z7,z16,z5])],[(0,[z76,z32,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z878]),(0,[z1,z7,z3,z15,z787,z5]),(0,[z0,z1,z3,z266,z29,z5]),(0,[z0,z1,z7,z3,z4,z750])],[(0,[z0,z1,z879,z3,z4,z5]),(0,[z277,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z880,z5]),(0,[z231,z7,z3,z4,z5,z86]),(0,[z0,z1,z7,z3,z120,z173]),(0,[z0,z1,z136,z7,z4,z12]),(0,[z0,z1,z410,z3,z4,z47])]],
   [[(0,[z0,z1,z7,z3,z4,z47])],[(0,[z0,z1,z7,z3,z4,z881]),(0,[z882,z1,z7,z3,z4,z5]),(0,[z0,z1,z99,z192,z4,z47]),(0,[z0,z1,z7,z3,z215,z12]),(0,[z0,z1,z3,z183,z4,z12]),(0,[z0,z1,z7,z4,z479,z12]),(0,[z0,z1,z7,z364,z4,z12])],[(0,[z0,z1,z396,z7,z3,z4])],[(0,[z0,z1,z7,z883,z4,z5]),(0,[z0,z1,z7,z3,z215,z5]),(0,[z0,z1,z3,z183,z4,z5]),(0,[z0,z1,z94,z7,z4,z750])],[(0,[z0,z1,z7,z3,z4,z884]),(0,[z0,z1,z885,z3,z4,z5]),(0,[z0,z1,z99,z192,z215,z5]),(0,[z0,z1,z72,z3,z4,z580])],[(0,[z0,z1,z7,z3,z886,z4]),(0,[z76,z887,z7,z3,z4,z5]),(0,[z191,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z888]),(0,[z0,z1,z3,z725,z4,z5]),(0,[z0,z1,z24,z183,z78,z5])],[(0,[z0,z1,z889,z3,z4,z5]),(0,[z0,z713,z7,z3,z4,z5]),(0,[z0,z1,z542,z3,z4,z49]),(0,[z0,z1,z890,z3,z4,z5]),(0,[z0,z1,z7,z3,z891,z5]),(0,[z0,z1,z7,z892,z4,z5])],[(0,[z557,z32,z7,z3,z4,z5]),(0,[z0,z154,z7,z3,z4,z12]),(0,[z0,z1,z58,z7,z3,z381])]],
   [[(0,[z0,z1,z7,z3,z4,z893]),(0,[z0,z713,z37,z3,z4,z5]),(0,[z0,z1,z620,z88,z4,z5]),(0,[z0,z1,z7,z3,z9,z57])],[(0,[z0,z154,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z894,z5]),(0,[z0,z236,z37,z3,z4,z12])],[(0,[z0,z1,z7,z3,z4,z895]),(0,[z0,z241,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z896]),(0,[z0,z7,z3,z4,z5,z897]),(0,[z0,z1,z177,z3,z4,z292]),(0,[z0,z1,z7,z24,z805,z5]),(0,[z0,z1,z7,z4,z5,z750])],[(0,[z0,z236,z37,z3,z4,z5]),(0,[z0,z1,z7,z4,z512,z12]),(0,[z0,z1,z7,z3,z4,z898]),(0,[z0,z1,z7,z24,z78,z75])],[(0,[z0,z1,z899,z3,z4,z5]),(0,[z0,z241,z7,z3,z4,z5]),(0,[z0,z900,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z901]),(0,[z0,z474,z37,z3,z4,z5]),(0,[z8,z277,z7,z33,z4,z5]),(0,[z0,z1,z7,z3,z4,z244])],[(0,[z0,z1,z7,z3,z902,z5]),(0,[z0,z1,z7,z3,z4,z903]),(0,[z904,z1,z7,z3,z4,z47])],[(0,[z0,z1,z905,z3,z4,z5]),(0,[z0,z1,z90,z3,z4,z175]),(0,[z0,z1,z906,z3,z4,z5]),(0,[z0,z65,z66,z3,z162,z5]),(0,[z0,z1,z7,z3,z4,z261])],[(1,[z1,z7,z763,z4,z5]),(0,[z105,z1,z7,z3,z123,z47]),(0,[z0,z1,z7,z3,z907,z5]),(0,[z0,z1,z7,z3,z4,z908]),(0,[z909,z1,z7,z3,z4,z5]),(0,[z910,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z911,z3,z4]),(0,[z310,z32,z7,z3,z4,z5]),(0,[z912,z1,z7,z3,z4,z5]),(0,[z0,z1,z23,z3,z78,z5])],[(0,[z0,z1,z7,z3,z913,z5]),(0,[z0,z1,z7,z3,z4,z914]),(0,[z0,z174,z7,z3,z4,z175]),(0,[z0,z1,z7,z388,z4,z12]),(0,[z161,z7,z3,z15,z4,z5])],[(0,[z0,z1,z915,z7,z3,z5]),(0,[z0,z916,z7,z3,z4,z5]),(0,[z0,z236,z713,z3,z4,z5]),(0,[z0,z1,z7,z917,z4,z5]),(0,[z0,z1,z918,z7,z3,z4]),(0,[z0,z919,z7,z3,z4,z5])],[(0,[z607,z149,z7,z3,z4,z5]),(0,[z153,z1,z740,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z920]),(0,[z0,z161,z7,z3,z4,z47]),(0,[z0,z921,z7,z3,z4,z5]),(0,[z0,z7,z3,z4,z12,z922])],[(0,[z0,z1,z7,z3,z4,z923]),(0,[z0,z1,z7,z3,z4,z924]),(0,[z0,z1,z925,z3,z4,z5]),(0,[z0,z1,z926,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z927])],[(0,[z0,z1,z7,z3,z928,z5]),(0,[z0,z1,z7,z3,z4,z929]),(0,[z0,z1,z7,z3,z4,z175]),(0,[z0,z930,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z9,z49]),(0,[z0,z204,z7,z3,z162,z5]),(0,[z326,z1,z7,z3,z4,z47])],[(0,[z149,z7,z3,z186,z4,z5]),(0,[z8,z191,z7,z33,z4,z5]),(0,[z0,z1,z177,z3,z4,z114])],[(0,[z0,z1,z7,z931,z4,z5]),(0,[z91,z461,z7,z3,z4,z131]),(0,[z0,z1,z23,z3,z4,z12]),(0,[z0,z1,z7,z3,z932,z47])]],
   [[(0,[z319,z340,z7,z3,z4,z5]),(0,[z8,z0,z7,z33,z4,z12])],[(0,[z0,z1,z7,z3,z4,z933]),(0,[z105,z161,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z934]),(0,[z0,z1,z23,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z749]),(0,[z0,z935,z7,z3,z4,z12])],[(0,[z8,z0,z7,z33,z4,z5]),(0,[z31,z50,z7,z3,z4,z86])],[(0,[z0,z1,z7,z3,z4,z936]),(0,[z0,z1,z83,z3,z9,z5]),(0,[z0,z1,z7,z3,z4,z937]),(0,[z0,z1,z3,z4,z824,z5]),(0,[z0,z935,z7,z3,z4,z5]),(0,[z0,z1,z721,z3,z4,z5]),(0,[z0,z1,z7,z3,z751,z59])],[(0,[z0,z1,z7,z3,z4,z938]),(0,[z0,z1,z7,z3,z43,z12]),(0,[z0,z1,z249,z88,z4,z47]),(0,[z0,z939,z7,z3,z4,z5])],[(0,[z0,z940,z7,z3,z4,z5]),(0,[z0,z1,z941,z7,z3,z4])],[(0,[z0,z1,z3,z4,z942,z5]),(0,[z0,z1,z396,z37,z3,z4])],[(0,[z0,z943,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z944]),(0,[z0,z1,z7,z4,z47,z17]),(0,[z945,z1,z7,z3,z4,z5]),(0,[z107,z1,z7,z3,z4,z12]),(0,[z0,z946,z7,z3,z4,z5])]],
   [[(0,[z587,z0,z93,z3,z4,z5]),(0,[z0,z1,z542,z3,z4,z47]),(0,[z0,z65,z7,z3,z947,z5]),(0,[z0,z1,z7,z3,z4,z19]),(0,[z0,z1,z3,z4,z12,z308])],[(0,[z0,z340,z7,z3,z4,z5]),(0,[z0,z1,z948,z7,z3,z4]),(0,[z0,z1,z2,z3,z4,z47]),(0,[z0,z949,z7,z3,z4,z5]),(0,[z0,z1,z178,z7,z16,z163]),(0,[z0,z1,z733,z3,z4,z5])],[(0,[z0,z887,z7,z3,z4,z5]),(0,[z1,z740,z87,z3,z4,z5]),(0,[z0,z950,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z951,z5]),(0,[z0,z11,z7,z3,z102,z5])],[(0,[z0,z1,z3,z4,z749,z114])],[(0,[z0,z1,z952,z3,z4,z5]),(0,[z31,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z343,z4,z47]),(0,[z0,z1,z7,z3,z4,z953]),(0,[z0,z954,z7,z3,z4,z12]),(0,[z0,z1,z58,z7,z3,z751])],[(0,[z0,z1,z7,z3,z4,z955]),(0,[z0,z65,z7,z3,z475,z5]),(0,[z956,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z24,z78,z187]),(0,[z957,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z958]),(0,[z0,z1,z7,z3,z4,z959]),(0,[z0,z954,z7,z3,z4,z5])]],
   [[(0,[z166,z1,z7,z3,z4,z131]),(0,[z0,z1,z7,z427,z78,z5]),(0,[z0,z1,z249,z88,z4,z244]),(0,[z0,z1,z249,z725,z4,z5]),(0,[z0,z1,z960,z3,z4,z5]),(0,[z0,z1,z961,z3,z4,z12])],[(0,[z319,z166,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z962]),(0,[z146,z1,z7,z62,z4,z164]),(0,[z0,z1,z963,z3,z4,z5]),(0,[z0,z1,z7,z684,z4,z47]),(0,[z0,z964,z7,z3,z4,z5])],[(0,[z319,z342,z1,z7,z3,z4]),(0,[z0,z35,z37,z3,z4,z5]),(0,[z0,z1,z961,z3,z4,z5]),(0,[z0,z1,z846,z3,z4,z12])],[(0,[z369,z149,z7,z3,z4,z5]),(0,[z0,z65,z7,z3,z162,z12]),(0,[z0,z1,z251,z3,z824,z5])],[(0,[z0,z1,z7,z3,z4,z965]),(0,[z0,z1,z7,z3,z337,z5]),(0,[z1,z7,z763,z140,z4,z5]),(0,[z0,z1,z966,z3,z4,z5]),(0,[z0,z1,z198,z7,z16,z5]),(0,[z0,z1,z967,z3,z4,z47])],[(0,[z0,z968,z7,z3,z4,z5]),(0,[z153,z1,z87,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z969]),(0,[z80,z1,z90,z140,z4,z5]),(0,[z319,z1,z7,z3,z4,z743]),(0,[z0,z1,z7,z3,z4,z970]),(0,[z0,z1,z99,z243,z4,z5]),(0,[z0,z65,z7,z3,z162,z5]),(0,[z0,z7,z3,z4,z5,z922])],[(0,[z0,z1,z7,z3,z4,z971]),(0,[z0,z1,z972,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z973])],[(0,[z0,z1,z974,z3,z4,z5]),(0,[z0,z1,z975,z3,z4,z5]),(0,[z0,z1,z7,z3,z9,z47]),(0,[z0,z1,z7,z24,z78,z47])]],
   [[(0,[z0,z1,z740,z3,z4,z5]),(0,[z80,z174,z7,z140,z4,z5])],[(0,[z146,z1,z7,z62,z4,z63]),(0,[z0,z1,z3,z183,z4,z75]),(0,[z0,z1,z227,z3,z4,z292])],[(0,[z80,z1,z7,z140,z4,z12]),(0,[z191,z1,z7,z3,z4,z57]),(0,[z0,z1,z26,z3,z4,z47]),(0,[z0,z1,z3,z29,z5,z224]),(0,[z976,z1,z7,z3,z4,z12])],[(0,[z0,z1,z7,z3,z4,z977]),(0,[z355,z1,z7,z140,z4,z5]),(0,[z0,z476,z7,z3,z4,z5]),(0,[z0,z978,z7,z3,z4,z5]),(0,[z506,z1,z100,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z979])],[(0,[z80,z1,z7,z140,z4,z5]),(0,[z0,z980,z7,z3,z4,z5]),(0,[z976,z1,z7,z3,z4,z5])],[(0,[z0,z1,z559,z7,z4,z12]),(0,[z0,z1,z7,z4,z805,z5])],[(0,[z0,z1,z2,z3,z4,z175]),(0,[z276,z1,z7,z3,z15,z12]),(0,[z0,z1,z7,z3,z4,z743]),(0,[z0,z7,z3,z4,z981,z5])],[(0,[z0,z476,z7,z3,z337,z5]),(0,[z982,z1,z7,z3,z4,z5]),(0,[z50,z231,z7,z3,z4,z86]),(0,[z0,z1,z178,z7,z805,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z983]),(0,[z276,z1,z7,z3,z15,z5]),(0,[z0,z1,z7,z4,z600,z12]),(0,[z0,z1,z177,z3,z4,z609])],[(0,[z887,z149,z7,z3,z4,z5]),(0,[z269,z149,z7,z3,z4,z12]),(0,[z0,z1,z984,z3,z4,z5]),(0,[z0,z1,z3,z29,z824,z5])],[(0,[z583,z149,z7,z3,z4,z5]),(0,[z0,z1,z985,z7,z3,z4]),(0,[z8,z0,z542,z33,z4,z5]),(0,[z0,z1,z3,z4,z5,z308])],[(0,[z0,z1,z986,z3,z4,z5]),(0,[z0,z1,z987,z3,z4,z5]),(0,[z431,z0,z7,z3,z4,z86])],[(0,[z0,z1,z7,z418,z4,z47]),(0,[z0,z1,z7,z3,z135,z47])],[(0,[z0,z1,z988,z7,z4,z5]),(0,[z648,z1,z7,z3,z15,z5]),(0,[z0,z1,z7,z3,z4,z989]),(0,[z0,z1,z7,z3,z4,z990])],[(0,[z319,z1,z7,z3,z4,z210]),(0,[z146,z1,z7,z62,z4,z5]),(0,[z0,z1,z7,z3,z4,z991]),(0,[z0,z1,z83,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z378]),(0,[z50,z0,z7,z3,z4,z86]),(0,[z0,z1,z7,z616,z4,z12]),(0,[z0,z1,z178,z7,z16,z12])],[(0,[z80,z1,z7,z140,z4,z225]),(0,[z191,z1,z7,z3,z4,z49])]],
   [[(0,[z0,z1,z992,z3,z4,z5]),(0,[z993,z0,z1,z7,z3,z4])],[(1,[z887,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z994,z4]),(0,[z0,z1,z7,z3,z4,z995]),(0,[z0,z1,z7,z3,z422,z751])],[(0,[z0,z996,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z751])],[(0,[z0,z1,z7,z3,z4,z997]),(0,[z0,z998,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z538,z12]),(0,[z0,z1,z177,z518,z3,z4])],[(0,[z703,z32,z7,z3,z4,z5]),(0,[z277,z1,z7,z3,z538,z5]),(0,[z999,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z1000,z5]),(0,[z191,z1,z83,z3,z4,z5]),(0,[z0,z1,z7,z3,z538,z5]),(0,[z8,z0,z7,z33,z4,z57]),(0,[z0,z1,z1001,z3,z4,z5]),(0,[z0,z169,z7,z170,z4,z47]),(0,[z0,z1,z1002,z3,z4,z5]),(0,[z0,z1,z28,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z1003]),(0,[z0,z1,z113,z3,z4,z749])],[(0,[z0,z1,z7,z3,z1004,z5]),(0,[z0,z1,z23,z3,z16,z5])],[(0,[z0,z1,z7,z527,z4,z12]),(0,[z0,z1,z7,z3,z4,z1005]),(0,[z0,z1,z23,z3,z4,z75])]],
   [[(0,[z0,z1,z7,z3,z1006,z5]),(0,[z1007,z1,z7,z3,z4,z5]),(0,[z0,z1,z23,z24,z78,z5])],[(0,[z0,z1,z7,z3,z4,z1008]),(0,[z340,z7,z3,z4,z5,z131]),(0,[z8,z0,z7,z33,z9,z5]),(0,[z0,z1,z251,z3,z129,z30]),(0,[z0,z1,z7,z3,z824,z5]),(0,[z0,z1,z7,z3,z4,z1009])],[(0,[z0,z461,z7,z3,z4,z5]),(0,[z0,z829,z7,z3,z4,z5]),(0,[z326,z65,z7,z3,z4,z5]),(0,[z0,z1,z66,z3,z4,z12]),(0,[z0,z1,z1010,z3,z4,z5])],[(0,[z484,z1,z87,z3,z4,z5]),(0,[z0,z1,z1011,z3,z4,z5]),(0,[z1012,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z491,z4,z12])],[(0,[z0,z1,z7,z3,z1013,z5]),(0,[z0,z1,z66,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1014]),(0,[z0,z1,z251,z3,z30,z12]),(0,[z0,z1,z3,z183,z4,z187])],[(0,[z634,z1,z7,z3,z15,z5]),(0,[z0,z1,z2,z3,z337,z5])],[(0,[z0,z1015,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z1016,z5]),(0,[z0,z1,z251,z3,z30,z5]),(0,[z0,z1,z7,z4,z750,z12])],[(0,[z0,z1,z7,z3,z1017,z5]),(0,[z0,z1018,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1019])]],
   [[(0,[z468,z149,z7,z3,z4,z5]),(0,[z0,z7,z3,z4,z5,z844]),(0,[z0,z1,z7,z286,z4,z47]),(0,[z0,z1,z7,z3,z4,z1020]),(0,[z0,z1,z7,z3,z753,z47])],[],[(0,[z0,z188,z7,z3,z4,z12]),(0,[z0,z1,z99,z192,z4,z261])],[(0,[z0,z1,z7,z725,z4,z5]),(0,[z0,z919,z7,z3,z4,z12])],[(0,[z0,z188,z7,z3,z4,z5]),(0,[z0,z1,z1021,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1022]),(0,[z0,z1,z251,z3,z349,z5])],[(0,[z80,z1,z2,z140,z4,z5]),(0,[z8,z0,z7,z738,z4,z5]),(0,[z0,z1,z7,z3,z215,z47]),(0,[z0,z1,z3,z183,z4,z47]),(0,[z0,z1,z1023,z3,z4,z5])],[(0,[z269,z887,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z164]),(0,[z709,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z947,z5]),(0,[z326,z7,z3,z102,z4,z5])],[(0,[z0,z1024,z7,z3,z4,z5]),(0,[z0,z1,z410,z3,z118,z4])]],
   [[(0,[z50,z0,z7,z3,z4,z685])],[(0,[z191,z1,z7,z3,z4,z47]),(0,[z1025,z1,z7,z3,z4,z5]),(0,[z0,z1,z239,z3,z824,z5])],[(0,[z0,z1,z83,z3,z4,z57])],[(0,[z130,z1,z100,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z1026])],[(0,[z0,z320,z1,z7,z3,z4]),(0,[z0,z1027,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1028])],[(0,[z0,z236,z37,z3,z4,z47]),(0,[z0,z1,z251,z3,z380,z5])],[(0,[z0,z1,z7,z3,z4,z63]),(0,[z0,z241,z7,z3,z4,z47]),(0,[z0,z11,z7,z3,z947,z5]),(0,[z0,z1029,z7,z3,z4,z5])],[(0,[z1030,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z296])]],
   [[(0,[z602,z149,z7,z3,z4,z5]),(0,[z157,z149,z7,z3,z4,z5]),(0,[z0,z1,z1031,z3,z4,z5]),(0,[z0,z174,z90,z3,z4,z5]),(0,[z1032,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1033]),(0,[z0,z1,z99,z192,z4,z296])],[(0,[z0,z1,z7,z3,z1034,z5]),(0,[z0,z1,z7,z3,z4,z1035]),(0,[z0,z1,z7,z3,z4,z1036]),(0,[z0,z1037,z7,z3,z4,z5]),(0,[z0,z1,z1038,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1039])],[(0,[z0,z1040,z7,z3,z4,z5]),(0,[z0,z1041,z7,z3,z4,z5]),(0,[z0,z340,z7,z3,z4,z12]),(0,[z1042,z1,z7,z3,z4,z5]),(0,[z0,z1,z23,z3,z4,z187])],[(0,[z0,z1,z99,z3,z215,z5])],[(0,[z0,z1,z1043,z7,z3,z5]),(0,[z0,z1,z90,z3,z4,z5]),(0,[z130,z1,z740,z3,z4,z5]),(0,[z0,z11,z7,z3,z102,z12]),(0,[z0,z1,z99,z682,z4,z5])],[(0,[z0,z1,z7,z1044,z4,z5]),(0,[z0,z1,z542,z3,z538,z5]),(0,[z0,z7,z3,z947,z162,z5]),(0,[z0,z1,z192,z725,z4,z5]),(1,[z0,z1,z3,z824,z5]),(0,[z0,z1,z1045,z3,z4,z5])],[(0,[z0,z1,z7,z3,z5,z1046]),(0,[z1,z7,z3,z4,z743,z131])],[(0,[z0,z174,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1047]),(0,[z146,z476,z7,z3,z4,z5]),(0,[z0,z1,z83,z3,z4,z49])]],
   [[(0,[z166,z269,z149,z7,z3,z4]),(0,[z0,z1,z90,z3,z337,z5]),(0,[z0,z1,z7,z3,z1048,z5]),(0,[z0,z1049,z7,z3,z4,z5]),(0,[z0,z1,z7,z4,z47,z12])],[(0,[z0,z1,z7,z3,z4,z12]),(0,[z76,z32,z7,z3,z4,z5]),(0,[z615,z149,z7,z3,z4,z5]),(0,[z563,z149,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1050]),(0,[z0,z1,z3,z1051,z4,z5])],[(0,[z277,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1052]),(0,[z0,z1,z7,z687,z4,z47]),(0,[z0,z1,z444,z7,z3,z59]),(0,[z0,z1,z3,z4,z47,z1053])],[(0,[z0,z1,z7,z3,z4,z5]),(0,[z149,z7,z3,z423,z4,z5]),(0,[z0,z174,z7,z3,z337,z5]),(0,[z0,z1054,z1,z7,z3,z4]),(0,[z0,z1055,z7,z3,z4,z5]),(0,[z0,z1,z7,z414,z4,z12]),(0,[z0,z1,z23,z3,z4,z47])],[(0,[z166,z0,z7,z3,z4,z86]),(0,[z8,z0,z7,z33,z4,z47]),(0,[z0,z1,z99,z192,z4,z5]),(1,[z0,z1,z7,z805,z5]),(0,[z46,z0,z7,z3,z4,z685])],[(0,[z0,z1,z1056,z7,z3,z4]),(0,[z76,z104,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1057]),(0,[z476,z7,z3,z140,z4,z5]),(0,[z0,z1,z7,z3,z337,z12]),(0,[z0,z7,z3,z947,z4,z5]),(0,[z0,z1,z7,z78,z805,z5])],[(0,[z0,z1,z94,z7,z4,z12]),(0,[z1058,z0,z7,z3,z4,z12])],[(0,[z0,z476,z90,z3,z4,z5]),(0,[z0,z1,z90,z3,z4,z225]),(0,[z0,z7,z3,z102,z947,z5])]],
   [[(0,[z0,z1,z7,z3,z43,z47]),(0,[z1058,z0,z7,z3,z4,z5])],[(0,[z0,z943,z7,z3,z4,z47]),(0,[z0,z1,z1059,z3,z4,z5])],[(0,[z0,z174,z7,z3,z4,z225]),(0,[z0,z1,z7,z3,z4,z1060]),(0,[z0,z27,z340,z7,z3,z4])],[(0,[z0,z1,z7,z3,z787,z5]),(0,[z1061,z1,z7,z3,z4,z5]),(0,[z107,z1,z7,z3,z4,z47])],[(0,[z0,z476,z7,z3,z4,z12])],[],[(0,[z0,z1,z7,z3,z4,z225]),(0,[z0,z1,z7,z56,z4,z12]),(0,[z0,z1,z501,z3,z4,z12]),(0,[z0,z1,z7,z3,z4,z1062]),(0,[z0,z1,z3,z4,z45,z749])],[(0,[z0,z1,z396,z93,z3,z4]),(0,[z0,z1,z7,z3,z1063,z4]),(0,[z742,z1,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1053])]],
   [[(0,[z0,z1,z501,z3,z4,z5]),(0,[z904,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z71,z4,z12]),(0,[z0,z1,z785,z3,z4,z5])],[(0,[z0,z634,z7,z3,z102,z5]),(0,[z0,z1,z7,z1064,z4,z5]),(0,[z0,z1,z7,z3,z4,z1065]),(0,[z0,z1,z22,z177,z3,z4])],[(0,[z0,z1,z7,z3,z4,z1066]),(0,[z0,z1,z7,z3,z337,z225]),(0,[z105,z1,z7,z3,z123,z5]),(0,[z39,z0,z93,z3,z4,z12])],[(0,[z0,z1,z7,z664,z4,z12])],[(0,[z0,z149,z26,z3,z4,z5]),(0,[z0,z1,z757,z7,z3,z5]),(0,[z39,z0,z93,z3,z4,z5]),(0,[z50,z0,z7,z3,z4,z897]),(0,[z0,z1,z7,z3,z209,z422])],[(0,[z166,z0,z27,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z1067])],[(0,[z319,z27,z149,z7,z3,z4]),(0,[z0,z1,z7,z3,z1068,z5]),(0,[z50,z0,z340,z7,z3,z4]),(0,[z39,z0,z713,z3,z4,z5]),(0,[z326,z1,z7,z3,z4,z12]),(0,[z0,z1,z177,z3,z190,z4]),(0,[z1069,z1,z7,z3,z4,z5])],[(0,[z146,z1,z7,z62,z4,z12]),(0,[z0,z679,z93,z3,z4,z5])]],
   [[(0,[z326,z1,z7,z3,z4,z5]),(0,[z146,z1,z7,z159,z4,z5]),(0,[z0,z1,z7,z3,z4,z1070]),(0,[z0,z1,z7,z3,z4,z1071]),(0,[z0,z1,z139,z3,z4,z409])],[(0,[z153,z1,z87,z3,z4,z47]),(0,[z0,z1072,z7,z3,z4,z5]),(0,[z0,z476,z7,z3,z4,z225]),(0,[z0,z1073,z7,z3,z4,z5]),(0,[z0,z1,z7,z1074,z4,z5]),(0,[z0,z7,z3,z4,z897,z86]),(0,[z0,z1075,z7,z3,z4,z12])],[(0,[z355,z0,z7,z33,z4,z5]),(0,[z0,z1,z1076,z7,z4,z5]),(0,[z0,z1,z7,z3,z932,z5])],[(0,[z0,z1,z1077,z7,z3,z4]),(0,[z0,z1075,z7,z3,z4,z5]),(0,[z0,z169,z7,z170,z4,z378]),(0,[z0,z1,z203,z7,z4,z12]),(0,[z0,z1,z7,z1078,z4,z5]),(0,[z0,z1,z7,z4,z12,z205])],[(0,[z0,z1,z3,z1079,z4,z5]),(0,[z0,z1,z7,z3,z1080,z5]),(0,[z0,z1,z1081,z3,z4,z5]),(0,[z301,z1,z7,z3,z123,z5]),(0,[z231,z27,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z43,z175]),(0,[z0,z1,z7,z3,z4,z125]),(1,[z0,z7,z3,z947,z5]),(0,[z0,z1,z249,z88,z4,z12])],[(0,[z80,z1,z7,z140,z4,z47]),(0,[z1082,z1,z7,z3,z4,z5]),(0,[z0,z1,z1083,z3,z4,z5])],[(0,[z149,z7,z3,z4,z5,z486]),(0,[z0,z1,z7,z1084,z4,z5]),(0,[z0,z1,z7,z3,z4,z1085]),(0,[z0,z1,z249,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z1086]),(0,[z0,z1,z3,z4,z12,z1087])]],
   [[(0,[z0,z1,z1088,z7,z4,z5]),(0,[z32,z887,z7,z3,z4,z5]),(0,[z0,z174,z2,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1089]),(0,[z0,z1,z7,z738,z4,z5]),(0,[z0,z1,z7,z1090,z4,z5]),(0,[z0,z1,z113,z3,z4,z580])],[(0,[z0,z1,z542,z3,z4,z12]),(0,[z0,z1,z7,z1091,z4,z5])],[(0,[z76,z449,z7,z3,z4,z5]),(0,[z153,z154,z87,z3,z4,z5]),(0,[z0,z1092,z7,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12]),(0,[z1,z7,z3,z4,z787,z5]),(0,[z277,z1,z542,z3,z4,z5]),(0,[z1093,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z897]),(0,[z0,z1,z251,z3,z505,z5])],[(0,[z0,z461,z7,z3,z4,z12]),(0,[z0,z1,z542,z3,z4,z5]),(0,[z0,z1,z1094,z3,z4,z5]),(0,[z0,z1,z7,z151,z4,z12])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z1095,z7,z3,z5]),(0,[z1096,z1,z7,z3,z4,z5])],[(0,[z269,z149,z7,z3,z4,z47]),(0,[z0,z1,z1097,z3,z4,z5]),(0,[z0,z1,z7,z3,z135,z261]),(0,[z1,z7,z3,z4,z12,z1098])],[(0,[z276,z161,z7,z3,z15,z5]),(0,[z31,z1,z7,z3,z4,z12])],[(0,[z0,z1,z7,z429,z4,z47]),(0,[z0,z1,z7,z3,z4,z1099]),(0,[z0,z1,z7,z3,z4,z163])]],
   [[(0,[z31,z1,z7,z3,z4,z5]),(0,[z319,z231,z1,z7,z3,z4]),(0,[z0,z1,z1100,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1101]),(0,[z0,z1,z7,z4,z47,z550])],[(0,[z0,z1,z7,z3,z1102,z5]),(0,[z1103,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1104]),(0,[z0,z1,z7,z253,z4,z750])],[(1,[z1,z740,z3,z4,z5]),(0,[z0,z1,z7,z3,z1105,z5]),(1,[z1,z7,z3,z787,z5]),(0,[z0,z1,z3,z1106,z4,z5]),(0,[z0,z1,z178,z7,z16,z47])],[(0,[z0,z32,z501,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1107]),(0,[z0,z1,z7,z3,z1108,z5]),(0,[z0,z1,z7,z3,z4,z1109]),(0,[z0,z1,z7,z805,z16,z5]),(0,[z0,z1,z7,z253,z4,z47])],[(0,[z552,z149,z7,z3,z4,z5]),(0,[z0,z1110,z7,z3,z4,z5])],[(0,[z8,z0,z7,z33,z4,z49]),(0,[z0,z1,z7,z3,z118,z422])],[(0,[z0,z1,z7,z1111,z4,z5]),(0,[z0,z1112,z7,z3,z4,z5]),(0,[z0,z1,z3,z1113,z4,z5])],[(0,[z1114,z0,z1,z7,z3,z4]),(0,[z0,z476,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z225]),(0,[z0,z1,z7,z3,z4,z1115]),(0,[z0,z1,z967,z3,z4,z5])]],
   [[(1,[z1,z7,z3,z4,z743]),(0,[z1116,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z9,z12]),(0,[z0,z1,z7,z24,z78,z12]),(0,[z0,z1,z1117,z3,z4,z12]),(0,[z0,z1,z7,z3,z118,z751])],[(0,[z0,z1,z7,z3,z4,z1118]),(0,[z0,z1,z7,z3,z1119,z5]),(0,[z91,z1,z7,z3,z4,z743]),(0,[z1120,z1,z7,z3,z4,z5]),(0,[z277,z1,z7,z3,z9,z5]),(0,[z0,z1,z7,z201,z4,z12]),(0,[z0,z1,z239,z3,z29,z12])],[(0,[z0,z1,z7,z3,z9,z5]),(0,[z0,z1,z1117,z3,z4,z5]),(0,[z0,z1,z7,z4,z47,z421]),(0,[z0,z1,z7,z24,z78,z5]),(0,[z0,z1,z1121,z3,z4,z5])],[(0,[z0,z1122,z7,z3,z4,z5]),(0,[z8,z0,z83,z33,z4,z5]),(0,[z0,z7,z170,z738,z4,z5]),(0,[z0,z1,z7,z3,z135,z296]),(0,[z0,z1,z239,z3,z29,z5])],[(0,[z0,z1,z7,z3,z4,z1123]),(0,[z0,z1,z555,z7,z16,z5]),(0,[z231,z1,z7,z3,z4,z12]),(0,[z0,z1,z7,z3,z1124,z5]),(0,[z0,z1,z1010,z3,z4,z47])],[(0,[z887,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1125]),(0,[z0,z1,z239,z3,z345,z5])],[(0,[z231,z1,z7,z3,z4,z5]),(0,[z0,z154,z7,z3,z4,z47]),(0,[z191,z1,z7,z3,z538,z5]),(0,[z0,z1,z66,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z749])],[(0,[z0,z1126,z7,z3,z4,z5]),(0,[z1,z7,z3,z787,z123,z5])]],
   [[(0,[z0,z1,z1127,z3,z4,z5]),(0,[z0,z1,z1128,z3,z4,z5]),(0,[z1129,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z639,z4,z47])],[(0,[z269,z320,z149,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z1130]),(0,[z0,z1,z7,z3,z4,z1131]),(0,[z0,z1,z3,z4,z5,z1087])],[(0,[z0,z1,z835,z3,z4,z5]),(0,[z0,z65,z26,z3,z162,z5]),(0,[z0,z1132,z7,z3,z4,z5])],[(1,[z0,z713,z3,z4,z5])],[(0,[z80,z1,z7,z140,z43,z5]),(0,[z0,z1,z7,z3,z4,z129])],[(0,[z1133,z0,z1,z7,z3,z4]),(0,[z0,z1,z90,z3,z4,z12]),(0,[z1134,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z1135,z5]),(0,[z0,z188,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z215,z261]),(0,[z0,z1,z7,z3,z5,z751])],[(0,[z0,z1,z7,z3,z4,z1136]),(0,[z0,z1,z1137,z3,z4,z5]),(0,[z0,z1,z7,z3,z135,z5]),(0,[z1,z7,z3,z4,z5,z1098])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 539).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1078).take 109) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1187)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [539, 539, 109] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 132).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 132).take 124).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [132, 124] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_39103

theorem PEqualNP.Outside.L_meta_39103 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209043680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4209043680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39103.solve