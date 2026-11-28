import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46192

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
  Nat.testBit (4277075680 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0044438408885a8a#64 ++ 0x04008887081110b5#64 ++ 0x02cc478c1998fffb#64 ++ 0x7a05988f183331ff#64 : BitVec 256),
   (0x005058b022a32e0c#64 ++ 0x0800a0b16045465c#64 ++ 0x257078f066e73e76#64 ++ 0xf64ae0f1e0cdce7c#64 : BitVec 256),
   (0x0981805987058510#64 ++ 0x90130300b30e0b0a#64 ++ 0xd98380ff8707c7ef#64 ++ 0xefb30701ff0e0f8f#64 : BitVec 256),
   (0x3602ad02f806f021#64 ++ 0x206c055a05f00de0#64 ++ 0xfe03ff03f807f85f#64 ++ 0xdffc07fe07f00ff0#64 : BitVec 256),
   (0x1fa8000355500041#64 ++ 0xc03f500006aaa000#64 ++ 0xbffc0003fff8003e#64 ++ 0x3f7ff80007fff000#64 : BitVec 256),
   (0x5fff76ec0000007e#64 ++ 0x00bffeedd8000000#64 ++ 0x5ffffffc00000001#64 ++ 0xfebffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [9, 6]⟩, ⟨.and, [11, 3]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1998fffb 0x7a05988f183331ff

def z1 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73e76 0xf64ae0f1e0cdce7c

def z2 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7ef 0xefb30701ff0e0f8f

def z3 : W := mkw 0x09d058b127a32e0c 0x8813a0b1624f465c 0xbdf078f3e7e73e7e 0xff7be0f1e7cfce7c

def z4 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff8003e 0x3f7ff80007fff000

def z5 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f85f 0xdffc07fe07f00ff0

def z6 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00000001 0xfebffffff8000000

def z7 : W := mkw 0x0000800080048000 0x0000010001000900 0xd80380038007c04f 0xcfb0070007000f80

def z8 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfffffffffff8003f 0xfffffffffffff000

def z9 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0x400380fc0007c7c1 0xc0800701f8000f8f

def z10 : W := mkw 0x09d1d8f9a7a7af1c 0x9813a3b1f34f4f5e 0xfdf3f8ffe7e7ffff 0xfffbe7f1ffcfcfff

def z11 : W := mkw 0x09d158f927a32f1c 0x9813a2b1f24f465e 0x25f078fc67e73ff6 0xf64be0f1f8cfce7f

def z12 : W := mkw 0x004442840000000a 0x0000888508000000 0x02cc478c0100c7eb 0x7a05988f1802018f

def z13 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbfbc0003ff78000c 0x0d7f780007fef000

def z14 : W := mkw 0x09c5c3dd8f8ddf9a 0x94138b87bb1f1bbf 0xdbcfc7ff9f9fffff 0xffb79f8fff3f3fff

def z15 : W := mkw 0x0000001002010400 0x0000000020040208 0x010000f006070666 0xe6020001e00c0e0c

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0x2570000066e00036 0x364ae00000cdc000

def z17 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd88380ff8107c7c9 0xc9b10701ff020f8f

def z18 : W := mkw 0x0000081022a32e00 0x080000102045465c 0x0000000000073e40 0x0000000000000e7c

def z19 : W := mkw 0x0040418008885a88 0x04008083001110b5 0x004040801998fffa 0x72008081003331ff

def z20 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0x4003ff000007f841 0xc08007fe00000ff0

def z21 : W := mkw 0x00545bb42aab7e8e 0x0c00a8b7685556fd 0x00007ffc0007ffc1 0xc00000fff8000fff

def z22 : W := mkw 0x004443940a895e8a 0x04008887281512bd 0x03cc47fc1f9fffff 0xfe07988ff83f3fff

def z23 : W := mkw 0x1600000250000001 0x002c000004a00000 0xbe000003f800001e 0x1f7c000007f00000

def z24 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4003fffc00000001 0xc08007fff8000000

def z25 : W := mkw 0x20008802f006a001 0x2040011005e00d40 0xa0000003e0070004 0x0140000007c00e00

def z26 : W := mkw 0x0981005907010510 0x90130200b20e020a 0x018000fc070007a0 0x20030001f80e000f

def z27 : W := mkw 0x0000010008005000 0x00000002001000a0 0x020047001800f85b 0x5a04008e003001f0

def z28 : W := mkw 0x3602ac02f006a021 0x206c055805e00d40 0xfc03b803e0070004 0x85f8077007c00e00

def z29 : W := mkw 0x0000010008885a80 0x04000002001110b5 0x000000001998fffa 0x00000000003331ff

def z30 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5d33b87000000000 0x84ba6770e0000000

def z31 : W := mkw 0x09d1d0f98705851c 0x9013a3a1f30e0b0a 0xddf3f8ff8707c7ef 0xffbbe7f1ff0e0f8f

def z32 : W := mkw 0x1ff850a35550004d 0xc03ff0a146aaa000 0xbffc78f3fff8003e 0xff7ff8f1e7fff000

def z33 : W := mkw 0x1f83244800000030 0x003f064890000000 0x5f83fffc00000001 0xfebf07fff8000000

def z34 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc0100c7eb 0xfebffffff802018f

def z35 : W := mkw 0x0000801187058500 0x90000100230e0b0a 0x8000000386070004 0x01000000070c0e00

def z36 : W := mkw 0x1fa8001357510441 0xc03f500026aea208 0xbffc00f3ffff067e 0xff7ff801e7fffe0c

def z37 : W := mkw 0x09a8000105500040 0xc0135000020aa000 0x99fc000387f8002e 0x2f33f800070ff000

def z38 : W := mkw 0x09d158f822a32e1c 0x0813a2b1f045465c 0x7df3f8fc66e73e77 0xfefbe7f1f8cdce7c

def z39 : W := mkw 0x09d5dbfdafafff9e 0x9c13abb7fb5f5fff 0xffffffffffffffff 0xffffffffffffffff

def z40 : W := mkw 0x0004030408085082 0x04000806081010a1 0x028c070c1918c189 0x0805180e18323183

def z41 : W := mkw 0x5fff77ec08885afe 0x04bffeefd81110b5 0x5ffffffc1998fffb 0xfebffffff83331ff

def z42 : W := mkw 0x0000081022a32e00 0x080000102045465c 0x2000000066e73e76 0x0040000000cdce7c

def z43 : W := mkw 0x0010183022232404 0x0800203060444648 0x2530387066670004 0x844a6070e0ccce00

def z44 : W := mkw 0x0004030408085082 0x04000806081010a1 0x028c078c1918c7eb 0x6a05180f1832318f

def z45 : W := mkw 0x1fa9805bd7558551 0xd03f5300b7aeab0a 0xffff80ffffffc7ff 0xffffff01ffffff8f

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000c0100c189 0x0801000018020183

def z47 : W := mkw 0x0000081022232400 0x0800001020444648 0x2000000066670004 0x0040000000ccce00

def z48 : W := mkw 0x09a8000105500040 0xc0135000020aa000 0x03fc00001ff8003a 0x3a07f800003ff000

def z49 : W := mkw 0x5fef67cc08885afa 0x04bfdecf981110b5 0x5acfc78c1998fffb 0x7ab59f8f183331ff

def z50 : W := mkw 0x3602ac02f006a021 0x206c055805e00d40 0xfe03ff03e0070005 0xdffc07fe07c00e00

def z51 : W := mkw 0x005050b002a10e0c 0x0800a0a16005421c 0x017000f006e00620 0x2002e001e00dc00c

def z52 : W := mkw 0x20008912faa7fe01 0x2840011225f54ffc 0xa0000003fee7fe7e 0x0140000007fdcffc

def z53 : W := mkw 0x3652fdb2faa7fe2d 0x286ca5fb65f54ffc 0xff73fff3fee7fe7f 0xfffee7ffe7fdcffc

def z54 : W := mkw 0x567e76a40000006e 0x00acfced48000000 0x5e7fff0000000001 0xdebcfffe00000000

def z55 : W := mkw 0x0000000250000001 0x0000000004a00000 0xa0000003f800001e 0x0140000007f00000

def z56 : W := mkw 0x20008902f806f001 0x2040011205f00de0 0xa0000003f807f85e 0x0140000007f00ff0

def z57 : W := mkw 0x1faa240355500061 0xc03f544806aaa000 0xffffff03fff8003f 0xfffffffe07fff000

def z58 : W := mkw 0x167858b272f32e4d 0x482cf0b164e5e65c 0x277c78f07eff3e76 0xf64ef8f1e0fdfe7c

def z59 : W := mkw 0x09a8000000000040 0x0013500000000000 0x01fc000000000000 0x2003f80000000000

def z60 : W := mkw 0x005050b002a10e0c 0x0800a0a16005421c 0x257000f066e00636 0x364ae001e0cdc00c

def z61 : W := mkw 0x1fec43875dd85acb 0xc43fd8870ebbb0b5 0xbffc478ffff8ffff 0x7f7ff88f1ffff1ff

def z62 : W := mkw 0x36022d0278027021 0x206c045a04f004e0 0x26007f007800f85b 0x5a4c00fe00f001f0

def z63 : W := mkw 0x0000801187058500 0x90000100230e0b0a 0x800000038707c7ee 0x01000000070e0f8f

def z64 : W := mkw 0x0000010008885a80 0x04000002001110b5 0x02cc00001998fffa 0x3a059800003331ff

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080008c010007a0 0x200100011802000f

def z66 : W := mkw 0x5faf274c080850f2 0x04bf5e4e981010a1 0x5a8f870c1918c189 0x08b51f0e18323183

def z67 : W := mkw 0x5ffff6fd8705857e 0x90bfffedfb0e0b0a 0xdfffffff8707c7ef 0xffbfffffff0e0f8f

def z68 : W := mkw 0x7ffffffefaa7fe7f 0x28fffffffdf54ffc 0xfffffffffee7fe7f 0xfffffffffffdcffc

def z69 : W := mkw 0x0004030408885a82 0x04000806081110b5 0x028c070c1998fffb 0x0805180e183331ff

def z70 : W := mkw 0x005050a00000000c 0x0000a0a140000000 0x057078f000000000 0xf60ae0f1e0000000

def z71 : W := mkw 0x09a8000105500040 0xc0135000020aa000 0x01fc000007f80020 0x2003f800000ff000

def z72 : W := mkw 0x004442840000000a 0x0000888508000000 0x02cc478c00000001 0x7a05988f18000000

def z73 : W := mkw 0x1fa8000000000040 0x003f500000000000 0x1ffc00001998003a 0x3e3ff80000333000

def z74 : W := mkw 0x0000080020022000 0x0000001000400440 0x2400780060073856 0xd64800f000c00e70

def z75 : W := mkw 0x49d776ec0000003e 0x0093aeedd8000000 0x5983fffc00000001 0xeeb307fff8000000

def z76 : W := mkw 0x7657ffeef806f03f 0x20ecafffddf00de0 0xfe03fffff807f85f 0xdffc07fffff00ff0

def z77 : W := mkw 0x1fec43875dd85acb 0xc43fd8870ebbb0b5 0xbffc4703fff8383e 0x3f7ff88e07fff070

def z78 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0x4203ff001807f85b 0xda8407fe00300ff0

def z79 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x9bfc00039ff80028 0x2937f800073ff000

def z80 : W := mkw 0x0040408000800a08 0x0000808100010014 0x0040408000803e72 0x720080810001007c

def z81 : W := mkw 0x0001004800000010 0x0000020090000000 0x400380fc00000001 0xc0800701f8000000

def z82 : W := mkw 0x5fff76fd0701057e 0x90bffeedfa0e020a 0x5ffffffc070007a1 0xfebffffff80e000f

def z83 : W := mkw 0x09a8000355500041 0xc013500006aaa000 0xa1fc0003fff8003e 0x2143f80007fff000

def z84 : W := mkw 0x5fff76ee5000007f 0x00bffeeddca00000 0xfffffffff800001f 0xfffffffffff00000

def z85 : W := mkw 0x49fd5afc22a32e5e 0x0893fab5f845465c 0x25fc78fc66e73e76 0xf64bf8f1f8cdce7c

def z86 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x028c478c1918ffc9 0x4805188f183231ff

def z87 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xfdf380ffe7e7c7ff 0xfffbe701ffcfcf8f

def z88 : W := mkw 0x0981004800000010 0x0013020090000000 0x598380fc00000001 0xeeb30701f8000000

def z89 : W := mkw 0x00545bb42aab7e8e 0x0c00a8b7685556fd 0x27fc7ffc7fffffff 0xfe4ff8fff8ffffff

def z90 : W := mkw 0x5fff7efc22a32e7e 0x08bffefdf845465c 0x7ffffffc66e73e77 0xfefffffff8cdce7c

def z91 : W := mkw 0x09ec428505d80aca 0xc413d8850a0bb015 0x01fc008c07f807a0 0x2003f801180ff00f

def z92 : W := mkw 0x3646ef86f88efaab 0x246c8ddf0df11df5 0xfecfff8ff99fffff 0xfffd9fff1ff33fff

def z93 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x00cc008c019807a0 0x200198011803300f

def z94 : W := mkw 0x09c1c0d987858f18 0x90138381b30f0b1e 0xd9c3c0ff8787ffff 0xffb38781ff0f0fff

def z95 : W := mkw 0x0980000105000000 0x80130000020a0000 0x998000038700002e 0x2f330000070e0000

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080008c00000001 0x6a01000118000000

def z97 : W := mkw 0x3602ac02f006a021 0x206c055805e00d40 0xfc03b803e007c04f 0xcff8077007c00f80

def z98 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x27fc78f07fff3e7e 0xfe4ff8f1e0fffe7c

def z99 : W := mkw 0x5faf264c00000072 0x00bf5e4c98000000 0x5fff870c00000001 0x3ebfff0e18000000

def z100 : W := mkw 0x1f80000355000001 0x803f000006aa0000 0xbf800003ff00003e 0x3f7f000007fe0000

def z101 : W := mkw 0x1602a40080048020 0x002c054801000900 0xde03ff038007c04f 0xdfbc07fe07000f80

def z102 : W := mkw 0x1fa8000000000040 0x003f500000000000 0x1ffc000000000000 0x3e3ff80000000000

def z103 : W := mkw 0x0980801187058500 0x90130100230e0b0a 0x998000038707c7ee 0x2f330000070e0f8f

def z104 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x2570787066e73814 0x944ae0f0e0cdce70

def z105 : W := mkw 0x5fff77ef5dd85aff 0xc4bffeefdebbb0b5 0xfffffffffff8ffff 0xfffffffffffff1ff

def z106 : W := mkw 0x3faaac03f556a061 0xe07f555807eaad40 0xffffb803ffff003e 0xbfffff7007fffe00

def z107 : W := mkw 0x0000010008005000 0x00000002001000a0 0x0280478c1900fffb 0x7a05008f183201ff

def z108 : W := mkw 0x49ff76ec0000007e 0x0093feedd8000000 0x41fffffc00000001 0xe083fffff8000000

def z109 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380ff8607c7c5 0xc5b20701ff0c0f8f

def z110 : W := mkw 0x1ff858b022a32e4c 0x083ff0b16045465c 0x3ffc78f066e73e76 0xfe7ff8f1e0cdce7c

def z111 : W := mkw 0x1600000250000001 0x002c000004a00000 0x2600000078000010 0x104c000000f00000

def z112 : W := mkw 0x3f83ad5bff07f531 0xb07f075ab7fe0fea 0xff83ffffff07ffff 0xffff07fffffe0fff

def z113 : W := mkw 0x3faaad03fd56f061 0xe07f555a07faade0 0xffffff03fffff87f 0xfffffffe07fffff0

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080008c0100c7eb 0x6a0100011802018f

def z115 : W := mkw 0x0980000105000000 0x80130000020a0000 0x9880000381000008 0x0931000007020000

def z116 : W := mkw 0x7fffffffff07f57f 0xb0fffffffffe0fea 0xffffffffff07ffff 0xfffffffffffe0fff

def z117 : W := mkw 0x0981004905000010 0x80130200920a0000 0xd98380ff8700002f 0xefb30701ff0e0000

def z118 : W := mkw 0x0000081022a32e00 0x080000102045465c 0x210000f066e73e76 0xe6420001e0cdce7c

def z119 : W := mkw 0x5fff77ec08885afe 0x04bffeefd81110b5 0x5ffffffc0000ffc1 0xfebffffff80001ff

def z120 : W := mkw 0x0010183022a32e04 0x080020306045465c 0x2530387066e73e76 0x844a6070e0cdce7c

def z121 : W := mkw 0x5faf264c00000072 0x00bf5e4c98000000 0x5a8f870c00000001 0x08b51f0e18000000

def z122 : W := mkw 0x09a9005907510550 0xd0135200b20ea20a 0x01fc00fc07f807a0 0x2003f801f80ff00f

def z123 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc1998003b 0xfebffffff8333000

def z124 : W := mkw 0x2003ad58aa07f530 0x3040075ab1540fea 0x4003fffc0007ffc1 0xc08007fff8000fff

def z125 : W := mkw 0x567e76a40000006e 0x00acfced48000000 0x067c7f0000000000 0x100cf8fe00000000

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000800032 0x3200800000010000

def z127 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd903807386070004 0x85b20700e70c0e00

def z128 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0xdfffffff8700002f 0xffbfffffff0e0000

def z129 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x25f078fc67e7ffff 0xfe4be0f1f8cfcfff

def z130 : W := mkw 0x09c5c2dd8705851a 0x90138b85bb0e0b0a 0xdbcfc7ff8707c7ef 0xffb79f8fff0e0f8f

def z131 : W := mkw 0x36022d0278027021 0x206c045a04f004e0 0x26007f0078003810 0x104c00fe00f00070

def z132 : W := mkw 0x1628000250500041 0x402c500004a0a000 0x267c000078f80010 0x104cf80000f1f000

def z133 : W := mkw 0x005058a02002200c 0x0000a0b140400440 0x257078f060073856 0xf64ae0f1e0c00e70

def z134 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x024c470018983810 0x1004988e00313070

def z135 : W := mkw 0x1602240000000020 0x002c044800000000 0x5e03ff0000000001 0xdebc07fe00000000

def z136 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xff73ff03fee7f87f 0xfffee7fe07fdcff0

def z137 : W := mkw 0x3602a502d804d021 0x206c054a05b009a0 0xda0387039800c009 0x09b4070e07300180

def z138 : W := mkw 0x5fbb3c7822232474 0x08bf7678f0444648 0x7d33b87066670004 0x84fa6770e0ccce00

def z139 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x253078f066673e44 0xc44a60f1e0ccce7c

def z140 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x27fc478c7ff8ffff 0x7e4ff88f18fff1ff

def z141 : W := mkw 0x0000001002010400 0x0000000020040208 0x257000f066e70676 0xf64ae001e0cdce0c

def z142 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e03e30 0x304ae0f1e0cdc07c

def z143 : W := mkw 0x0000080020022000 0x0000001000400440 0x2570780066e73876 0xf64ae0f000cdce70

def z144 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000008c0000c7c1 0x400000011800018f

def z145 : W := mkw 0x1ff858b377f32e4d 0xc83ff0b166efe65c 0xbffc78f3ffff3e7e 0xff7ff8f1e7fffe7c

def z146 : W := mkw 0x0980000105000000 0x80130000020a0000 0x9900000386000004 0x05320000070c0000

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0x00cc000001980020 0x2001980000033000

def z148 : W := mkw 0x09919879a727a514 0x98132330f34e4f4a 0xfd33b873e6670004 0x85fa6770e7ccce00

def z149 : W := mkw 0x0981805bd7558511 0xd0130300b7aeab0a 0xf98380ffffffc7ff 0xeff30701ffffff8f

def z150 : W := mkw 0x7fffffeef806f07f 0x20ffffffddf00de0 0xfffffffff807f85f 0xfffffffffff00ff0

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400000003852 0x5200008000000070

def z152 : W := mkw 0x5ffd52ec0000005e 0x00bffaa5d8000000 0x1ffc00fc00000000 0x3e3ff801f8000000

def z153 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfc03ff03e007f845 0xc5f807fe07c00ff0

def z154 : W := mkw 0x49b9106800000054 0x00937220d0000000 0x0130007000000000 0x00026000e0000000

def z155 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5f33ff7000000001 0xdebe67fee0000000

def z156 : W := mkw 0x5fff76ee5050007f 0x40bffeeddca0a000 0x7ffffffc78f80011 0xfefffffff8f1f000

def z157 : W := mkw 0x1fa8000105500040 0xc03f5000020aa000 0x1ffc000007f80020 0x3e3ff800000ff000

def z158 : W := mkw 0x09a8000105500040 0xc0135000020aa000 0x25fc000067f80036 0x364bf80000cff000

def z159 : W := mkw 0x3652fda2f806f02d 0x206ca5fb45f00de0 0xff73fff3f807f85f 0xfffee7ffe7f00ff0

def z160 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0x4003807000070000 0x80800700e0000e00

def z161 : W := mkw 0x1ff858a375f22a4d 0xc83ff0b146ebe454 0xbffc7803fff8383e 0x3f7ff8f007fff070

def z162 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xdfffffff99180009 0xffbfffffff323000

def z163 : W := mkw 0x0981004800000010 0x0013020090000000 0x018000fc00000000 0x20030001f8000000

def z164 : W := mkw 0x49fd52ec0000005e 0x0093faa5d8000000 0x01fc00fc00000000 0x2003f801f8000000

def z165 : W := mkw 0x09d1d0f987a58f1c 0x9813a3a1f30f4b1e 0xd9f380ff87e7c7ef 0xefb3e701ff0fcf8f

def z166 : W := mkw 0x3faa2d037d527061 0xe07f545a06faa4e0 0xbffc7f03fff8383e 0x3f7ff8fe07fff070

def z167 : W := mkw 0x5ffff6ffd755857f 0xd0bfffedffaeab0a 0xffffffffffffc7ff 0xffffffffffffff8f

def z168 : W := mkw 0x098181598f05d510 0x90130302b31e0baa 0xdb83c7ff9f07ffff 0xffb7078fff3e0fff

def z169 : W := mkw 0x3f83ad4bfd06f131 0xb07f075a97fa0de2 0xfe83ff0ff907f9df 0xdffd07fe1ff20ff3

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x010000f000000000 0xe6020001e0000000

def z171 : W := mkw 0x3faaac03f556a061 0xe07f555807eaad40 0xfd33b803e6670004 0x85fa677007ccce00

def z172 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc470c1998f999 0x1805988e183331f3

def z173 : W := mkw 0x3faaa503dd54d061 0xe07f554a07baa9a0 0xffff8703fff8c03f 0x3fffff0e07fff180

def z174 : W := mkw 0x004442840000000a 0x0000888508000000 0x02cc478c1998003b 0x7a05988f18333000

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x02cc00001998003a 0x3a05980000333000

def z176 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbd300003e6600004 0x057a600007ccc000

def z177 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5db3b8fc00000001 0xeebb6771f8000000

def z178 : W := mkw 0x0040408000800a08 0x0000808100010014 0x2570408066e03e76 0x764ae08100cdc07c

def z179 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x27fc00007ff80030 0x304ff80000fff000

def z180 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x0000478c1998fffb 0x4000008f183331ff

def z181 : W := mkw 0x5fff7efc2223247e 0x08bffefdf8444648 0x7ffffffc66670005 0xfefffffff8ccce00

def z182 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc008ffff8c7ff 0x7f7ff8011ffff18f

def z183 : W := mkw 0x0010183022232404 0x0800203060444648 0x253038f066670666 0xe64a6071e0ccce0c

def z184 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x0000470000003800 0x0000008e00000070

def z185 : W := mkw 0x1fa801035d505041 0xc03f500206baa0a0 0xbffc4703fff8f87f 0x7f7ff88e07fff1f0

def z186 : W := mkw 0x49fd52ec0000005e 0x0093faa5d8000000 0x03fc47fc00000001 0x7a07f88ff8000000

def z187 : W := mkw 0x005058b02223240c 0x0800a0b160444648 0x257078f066670004 0xf64ae0f1e0ccce00

def z188 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x0000478c0000ffc1 0x4000008f180001ff

def z189 : W := mkw 0x1fa9805bd7558551 0xd03f5300b7aeab0a 0xdb8f80ff9f1fc7ef 0xefb71f01ff3e3f8f

def z190 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5f7fff7000000000 0x94befffee0000000

def z191 : W := mkw 0x4013346800000034 0x00802668d0000000 0x4003b87000000000 0x80800770e0000000

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000c04b 0x4a00000000000180

def z193 : W := mkw 0x5fff77ec08885afe 0x04bffeefd81110b5 0x5ffffffc18983811 0xfebffffff8313070

def z194 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x000078f000073e40 0xc00000f1e0000e7c

def z195 : W := mkw 0x5faf264c00000072 0x00bf5e4c98000000 0x5e8fff0c00000001 0xdebd1ffe18000000

def z196 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0xd80380ff8007c7cf 0xcfb00701ff000f8f

def z197 : W := mkw 0x0000801082058500 0x1000010021040b0a 0x000000000007c7c0 0x0000000000000f8f

def z198 : W := mkw 0x7fffffeef88efaff 0x24ffffffddf11df5 0xfffffffff99fffff 0xfffffffffff33fff

def z199 : W := mkw 0x09c443850d885a8a 0x841388870a1b10b5 0x9bcc478f9f98ffff 0x7f37988f1f3f31ff

def z200 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0xd803ff038007f84f 0xcfb007fe07000ff0

def z201 : W := mkw 0x09c5c2dd878d8f9a 0x94138b85bb0f1b1f 0xd9cf80ff879fc7ef 0xefb39f01ff0f3f8f

def z202 : W := mkw 0x005050a000800a0c 0x0000a0a140010014 0x057078f000803e72 0xf60ae0f1e001007c

def z203 : W := mkw 0x09818859a707a510 0x90130310b34e0f4a 0xfd83f8ffe707ffff 0xfffb07f1ffce0fff

def z204 : W := mkw 0x0000800080048000 0x0000010001000900 0x800000038007c04e 0x0100000007000f80

def z205 : W := mkw 0x004442840000000a 0x0000888508000000 0x0000478c00000001 0x4000008f18000000

def z206 : W := mkw 0x0000081022a32e00 0x080000102045465c 0x2570000066e73e76 0x364ae00000cdce7c

def z207 : W := mkw 0x0981005907010510 0x90130200b20e020a 0x598380fc070007a1 0xeeb30701f80e000f

def z208 : W := mkw 0x3606af06f80ef0a3 0x246c0d5e0df01de1 0xfe8fff0ff91ff9df 0xdffd1ffe1ff23ff3

def z209 : W := mkw 0x166c438658d85acb 0x442cd8870cb1b0b5 0x267c470078f83810 0x104cf88e00f1f070

def z210 : W := mkw 0x567e76a40000006e 0x00acfced48000000 0x077c7ff000000000 0xf60ef8ffe0000000

def z211 : W := mkw 0x0980000105000000 0x80130000020a0000 0x0180000007000020 0x20030000000e0000

def z212 : W := mkw 0x09f858b127f32e4c 0xc813f0b1624fe65c 0x25fc78f067ff3e76 0xf64bf8f1e0cffe7c

def z213 : W := mkw 0x0000080020022000 0x0000001000400440 0x2000000060073856 0x0040000000c00e70

def z214 : W := mkw 0x3faaa503dd54d061 0xe07f554a07baa9a0 0xda8f87039918c009 0x09b51f0e07323180

def z215 : W := mkw 0x7fbbbd6af806f075 0x20ff777ad5f00de0 0xff33ff73f807f85f 0xdffe67fee7f00ff0

def z216 : W := mkw 0x0000001002a10e00 0x080000002005421c 0x0000000006e00620 0x00000000000dc00c

def z217 : W := mkw 0x0981005907010510 0x90130200b20e020a 0x0100007006000000 0x00020000e00c0000

def z218 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5d33fffc00000001 0xc4ba67fff8000000

def z219 : W := mkw 0x0981804985048110 0x90130300930a0902 0xd883800f8100c189 0x09b107001f020183

def z220 : W := mkw 0x09a8000105500040 0xc0135000020aa000 0x0130000006600000 0x00026000000cc000

def z221 : W := mkw 0x005059b02aa37e0c 0x0800a0b3605546fc 0x27707ff07ee7fe7f 0xfe4ee0ffe0fdcffc

def z222 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380738707c7ee 0x85b20700e70e0f8f

def z223 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x247078f060e73e50 0xd048e0f1e0c1ce7c

def z224 : W := mkw 0x0000000105000000 0x80000000020a0000 0x800000038700002e 0x01000000070e0000

def z225 : W := mkw 0x2046ef84a88efaaa 0x24408ddf09511df5 0x4003ff8c0007ffc1 0xc08007ff18000fff

def z226 : W := mkw 0x0002240000000020 0x0000044800000000 0x4003ff0000000001 0xc08007fe00000000

def z227 : W := mkw 0x005050a00000000c 0x0000a0a140000000 0x017000f000000000 0x2002e001e0000000

def z228 : W := mkw 0x4007264c00000032 0x00800e4c98000000 0x4003870c00000001 0x0080070e18000000

def z229 : W := mkw 0x0044428400800a0a 0x0000888508010014 0x02cc478c00803e73 0x7a05988f1801007c

def z230 : W := mkw 0x1fa88003d5548041 0xc03f510007aaa900 0xffff8003ffffc07f 0xffffff0007ffff80

def z231 : W := mkw 0x09c543cc08885a9a 0x04138a87981110b5 0x5bcfc7fc1998fffb 0xfeb79f8ff83331ff

def z232 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x02cc478c019807a1 0x7a05988f1803300f

def z233 : W := mkw 0x3652fcb2f2a7ae2d 0x286ca5f965e54f5c 0xfd73f8f3e6e73e76 0xf7fae7f1e7cdce7c

def z234 : W := mkw 0x1602240250000021 0x002c044804a00000 0xfe03ff03f800001f 0xdffc07fe07f00000

def z235 : W := mkw 0x2050d9b2faa7fe0d 0x2840a1b365f54ffc 0xa57078f3fee7fe7e 0xf74ae0f1e7fdcffc

def z236 : W := mkw 0x00008811a7a7af00 0x98000110234f4f5e 0xa0000003e7e7fffe 0x0140000007cfcfff

def z237 : W := mkw 0x0981004905000110 0x90130200920a0002 0x0080000c01000180 0x0001000018020003

def z238 : W := mkw 0x004443840808508a 0x04008887081010a1 0x02cc478c1918c189 0x7a05988f18323183

def z239 : W := mkw 0x0000001107010500 0x90000000220e020a 0x00000000070007a0 0x00000000000e000f

def z240 : W := mkw 0x004443840800500a 0x00008887081000a0 0x02cc478c1800f85b 0x7a05988f183001f0

def z241 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbf7c0003fef80014 0x157ef80007fdf000

def z242 : W := mkw 0x563a342000000064 0x00ac746840000000 0x0430380000000000 0x0008607000000000

def z243 : W := mkw 0x098181598f8ddf90 0x94130302b31f1bbf 0xd98380ff9f9fffff 0xefb30701ff3f3fff

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400780000000000 0xd60800f000000000

def z245 : W := mkw 0x005453b40aa95e8e 0x0c00a8a7681552bd 0x03fc47fc1ff8fffb 0x7a07f88ff83ff1ff

def z246 : W := mkw 0x0040418008805a08 0x00008083001100b4 0x024047801880fe7b 0x7a04808f003101fc

def z247 : W := mkw 0x49fd52ec0000005e 0x0093faa5d8000000 0x59ff80fc00000001 0xeeb3ff01f8000000

def z248 : W := mkw 0x1628000355500041 0xc02c500006aaa000 0xa67c0003fff8003e 0x114cf80007fff000

def z249 : W := mkw 0x0980000355500001 0xc013000006aaa000 0xb9800003fff8003e 0x2f73000007fff000

def z250 : W := mkw 0x004442840000000a 0x0000888508000000 0x024c470000000000 0x1004988e00000000

def z251 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x9a8c000399180008 0x0935180007323000

def z252 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfa038703f807f85f 0x09f4070e07f00ff0

def z253 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x00cc008c1998fffa 0x20019801183331ff

def z254 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbd300003fff8003e 0x057a600007fff000

def z255 : W := mkw 0x2983ad59af07f530 0xb053075ab35e0fea 0xd983ffff8707ffef 0xefb307ffff0e0fff

def z256 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f8073814 0x95fc07fe07f00e70

def z257 : W := mkw 0x005058a020a22a0c 0x0800a0b140414454 0x2470780060e03810 0x1048e0f000c1c070

def z258 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x467ffffc00000001 0xd08cfffff8000000

def z259 : W := mkw 0x7fafa74ed804d073 0x20ff5f4e9db009a0 0xda8f870f9800c009 0x09b51f0e1f300180

def z260 : W := mkw 0x005050b002a10e0c 0x0800a0a16005421c 0x057078f006e00620 0xf60ae0f1e00dc00c

def z261 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x7ffffffc66e00037 0xfefffffff8cdc000

def z262 : W := mkw 0x2002a5008804d020 0x2040054a011009a0 0x400387000000c001 0x0080070e00000180

def z263 : W := mkw 0x1602240000000020 0x002c044800000000 0x5a03870000000001 0x08b4070e00000000

def z264 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe83ff8ff907ffff 0xfffd07ff1ff20fff

def z265 : W := mkw 0x0000800080048000 0x0000010001000900 0xd80380038000c009 0x09b0070007000180

def z266 : W := mkw 0x4057f6fc8205853e 0x1080afedf9040b0a 0x4003fffc0007c7c1 0xc08007fff8000f8f

def z267 : W := mkw 0x5fbb346b55500075 0xc0bf7668d6aaa000 0xfd33b873e6600004 0x85fa6770e7ccc000

def z268 : W := mkw 0x09c5c3cd8d8cdb9a 0x94138b879b1b19b7 0xdacfc78f9998fffb 0x7bb59f8f1f3331ff

def z269 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x5ffffffc00803e73 0xfebffffff801007c

def z270 : W := mkw 0x0000001002010400 0x0000000020040208 0x010000f006000620 0x20020001e00c000c

def z271 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f800f819 0x19fc07fe07f001f0

def z272 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xda03ff039807f849 0xc9b407fe07300ff0

def z273 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c0000ffc1 0x7a05988f180001ff

def z274 : W := mkw 0x567e76a40000006e 0x00acfced48000000 0x06fc7f8c00000001 0x7a0df8ff18000000

def z275 : W := mkw 0x3602ac02f006a021 0x206c055805e00d40 0xfe03b803f807001e 0x9ffc077007f00e00

def z276 : W := mkw 0x165274a00000002c 0x002ca4e940000000 0x5f73fff000000001 0xfebee7ffe0000000

def z277 : W := mkw 0x09919879a727a514 0x98132330f34e4f4a 0xfdb3b8ffe767c7ef 0xeffb6771ffcecf8f

def z278 : W := mkw 0x0000000355500001 0xc000000006aaa000 0x8000000399180008 0x0100000007323000

def z279 : W := mkw 0x49fd52fc02a10e5e 0x0893faa5f805421c 0x01fc00fc06e00620 0x2003f801f80dc00c

def z280 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x010078f006073e66 0xe60200f1e00c0e7c

def z281 : W := mkw 0x20008903fd56f001 0xe040011207faade0 0xa0000003fffff87e 0x0140000007fffff0

def z282 : W := mkw 0x0051d8f8a2a7af1c 0x1800a3b1f1454f5e 0x4003f8fc0007ffc1 0xc08007f1f8000fff

def z283 : W := mkw 0x5faf264c00000072 0x00bf5e4c98000000 0x5b8f87fc00000001 0xeeb71f0ff8000000

def z284 : W := mkw 0x1fa8000000000040 0x003f500000000000 0x3ffc000066e00036 0x3e7ff80000cdc000

def z285 : W := mkw 0x405552ec0000001e 0x0080aaa5d8000000 0x000000fc00000000 0x00000001f8000000

def z286 : W := mkw 0x0044c384888cda8a 0x04008987091119b5 0xdacfc78f999fffff 0xffb59f8f1f333fff

def z287 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03bf03f807c00d 0x8dfc077e07f00f80

def z288 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff86070005 0xefb30701ff0c0e00

def z289 : W := mkw 0x3602ad12fa07f421 0x206c055a25f40fe8 0xff03fff3fe07fe7f 0xfffe07ffe7fc0ffc

def z290 : W := mkw 0x1fa8000105000040 0x803f5000020a0000 0x9ffc00038700002e 0x3f3ff800070e0000

def z291 : W := mkw 0x7fbbbc6af006a075 0x20ff7778d5e00d40 0xfd33b873e0070004 0x85fa6770e7c00e00

def z292 : W := mkw 0x0040408000800a08 0x0000808100010014 0x02cc408019983e7a 0x7a0598810033307c

def z293 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x00cc008c0198c7eb 0x6a0198011803318f

def z294 : W := mkw 0x767e7fa67802706f 0x20ecfcff4cf004e0 0x267c7f0078003810 0x104cf8fe00f00070

def z295 : W := mkw 0x0000001002010400 0x0000000020040208 0x018000fc0707c7ef 0xee030001f80e0f8f

def z296 : W := mkw 0x1ff858b377f32e4d 0xc83ff0b166efe65c 0xbd7078f3e6e73e76 0xf77ae0f1e7cdce7c

def z297 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfecfff03f99ff87f 0xfffd9ffe07f33ff0

def z298 : W := mkw 0x0000800080048000 0x0000010001000900 0xd883808f8107c7ef 0xefb107011f020f8f

def z299 : W := mkw 0x1628000000000040 0x002c500000000000 0x067c000000000000 0x100cf80000000000

def z300 : W := mkw 0x407c52a40000004e 0x0080f8a548000000 0x007c000000000000 0x0000f80000000000

def z301 : W := mkw 0x0981804985048110 0x90130300930a0902 0xd883808f8100c7eb 0x6bb107011f02018f

def z302 : W := mkw 0x1fa9805987058550 0x903f5300b30e0b0a 0xdfff80ff8707c7ef 0xffbfff01ff0e0f8f

def z303 : W := mkw 0x164666840000002a 0x002c8ccd08000000 0x5ecfff8c00000001 0xfebd9fff18000000

def z304 : W := mkw 0x20008902f88efa81 0x2440011205f11df5 0xa0000003f99ffffe 0x0140000007f33fff

def z305 : W := mkw 0x1600080270022001 0x002c001004e00440 0xbe007803f807385e 0xdf7c00f007f00e70

def z306 : W := mkw 0x7ffff7eed804d07f 0x20ffffefddb009a0 0xdfffffff9800c009 0xffbfffffff300180

def z307 : W := mkw 0x362aad02f856f061 0x606c555a05f0ade0 0xfe7fff03f8fff85f 0xdffcfffe07f1fff0

def z308 : W := mkw 0x6057ffeca806f03e 0x20c0afffd9500de0 0x4003fffc0007f841 0xc08007fff8000ff0

def z309 : W := mkw 0x0004030408085082 0x04000806081010a1 0x0000070c0000c181 0x0000000e18000183

def z310 : W := mkw 0x000081118f8ddf80 0x94000102231f1bbf 0x800000039f9ffffe 0x01000000073f3fff

def z311 : W := mkw 0x0028000000500040 0x400050000000a000 0x007c000000f80000 0x0000f8000001f000

def z312 : W := mkw 0x005058a020a22a0c 0x0800a0b140414454 0x0000780000003800 0x000000f000000070

def z313 : W := mkw 0x0980000000000000 0x0013000000000000 0x1980000000000000 0x2e33000000000000

def z314 : W := mkw 0x0050d8b1a7a7af0c 0x9800a1b1634f4f5e 0xa57078f3e7e7fffe 0xf74ae0f1e7cfcfff

def z315 : W := mkw 0x005050a00000000c 0x0000a0a140000000 0x000078f000000000 0xc00000f1e0000000

def z316 : W := mkw 0x000009102aab7e80 0x0c000012205556fd 0x200000007ffffffe 0x0040000000ffffff

def z317 : W := mkw 0x09818859a7a7af10 0x98130310b34f4f5e 0xf98380ffe7e7ffff 0xeff30701ffcfcfff

def z318 : W := mkw 0x2000090278027001 0x2040001204f004e0 0x2000000078003810 0x0040000000f00070

def z319 : W := mkw 0x49fd52ed0550005e 0xc093faa5da0aa000 0x01fc00fc07f80020 0x2003f801f80ff000

def z320 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xffffffffe6600005 0xffffffffffccc000

def z321 : W := mkw 0x00545ab422ab2e8e 0x0c00a8b56845565d 0x25fc78fc67ff3ff6 0xf64bf8f1f8cffe7f

def z322 : W := mkw 0x49fd52ec00880ade 0x0493faa5d8011015 0x01fc00fc019807a0 0x2003f801f803300f

def z323 : W := mkw 0x09a8000105500040 0xc0135000020aa000 0x008c000001180000 0x0001180000023000

def z324 : W := mkw 0x1628000250500041 0x402c500004a0a000 0xbe7c0003f8f8001e 0x1f7cf80007f1f000

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z326 : W := mkw 0x1fa8000250000041 0x003f500004a00000 0xbffc0003f800001e 0x3f7ff80007f00000

def z327 : W := mkw 0x0000000355500001 0xc000000006aaa000 0xa0000003e6600004 0x0140000007ccc000

def z328 : W := mkw 0x5fff77ec0800507e 0x00bffeefd81000a0 0x5ffffffc1800f85b 0xfebffffff83001f0

def z329 : W := mkw 0x00545ba428aa7a8e 0x0c00a8b7485154f5 0x26fc7f8c79f8fffb 0x7a4df8ff18f3f1ff

def z330 : W := mkw 0x0010183022232404 0x0800203060444648 0x0000387000070000 0x80000070e0000e00

def z331 : W := mkw 0x0000800080048000 0x0000010001000900 0x400380000007c041 0xc080070000000f80

def z332 : W := mkw 0x0040489022a32e08 0x080080912045465c 0x2040408066e73e76 0x7240808100cdce7c

def z333 : W := mkw 0x0040408000800a08 0x0000808100010014 0x00c0408c0180fffb 0x7a018081180301ff

def z334 : W := mkw 0x562e260400000062 0x00ac5c4c08000000 0x020c070000000000 0x0004180e00000000

def z335 : W := mkw 0x166c438658d85acb 0x442cd8870cb1b0b5 0x26fc478c79f8fffb 0x7a4df88f18f3f1ff

def z336 : W := mkw 0x36022d0278027021 0x206c045a04f004e0 0x7e03ff0078003811 0xdefc07fe00f00070

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000000100002a 0x2a01000000020000

def z338 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xdbcf80ff9f9fc7ff 0xffb79f01ff3f3f8f

def z339 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000006000026 0x26020000000c0000

def z340 : W := mkw 0x49fd53ec08885ade 0x0493faa7d81110b5 0x03fc47fc1998fffb 0x7a07f88ff83331ff

def z341 : W := mkw 0x09c5c3dd8f8ddf9a 0x94138b87bb1f1bbf 0xd983c7ff8707ffef 0xefb3078fff0e0fff

def z342 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200470000000001 0x5a04008e00000000

def z343 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5effff0c00000001 0x18bdfffe18000000

def z344 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8700c7a9 0x29b30701ff0e018f

def z345 : W := mkw 0x0000010008885a80 0x04000002001110b5 0x0080008c1998fffb 0x6a010001183331ff

def z346 : W := mkw 0x1ffc5bb77ffb7ecf 0xcc3ff8b76efff6fd 0xbffc7fffffffffff 0xff7ff8ffffffffff

def z347 : W := mkw 0x16527cb022a32e2c 0x082ca4f96045465c 0x7f73fff066e73e77 0xfefee7ffe0cdce7c

def z348 : W := mkw 0x2046ef84a88efaaa 0x24408ddf09511df5 0x42cfff8c199ffffb 0xfa859fff18333fff

def z349 : W := mkw 0x0000000000800a00 0x0000000000010014 0x0000000000803e72 0x000000000001007c

def z350 : W := mkw 0x3feeef87fddefaeb 0xe47fdddf0ffbbdf5 0xffffff8fffffffff 0xffffffff1fffffff

def z351 : W := mkw 0x00444b84288a7a8a 0x04008897085114f5 0x26cc7f8c799fffff 0xfe4d98ff18f33fff

def z352 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbe8c0003f918001e 0x1f7d180007f23000

def z353 : W := mkw 0x005058a020a22a0c 0x0800a0b140414454 0x2570780066e03836 0x364ae0f000cdc070

def z354 : W := mkw 0x1fa9004b55500051 0xc03f520096aaa000 0xffff80fffff8003f 0xffffff01fffff000

def z355 : W := mkw 0x5fff76ed0550007e 0xc0bffeedda0aa000 0x5ffffffc07f80021 0xfebffffff80ff000

def z356 : W := mkw 0x40577efc22a32e3e 0x0880aefdf845465c 0x6573fffc66e73e77 0xf6cae7fff8cdce7c

def z357 : W := mkw 0x1fe8408355d00a49 0xc03fd08106aba014 0xbffc4083fff83e7e 0x7f7ff88107fff07c

def z358 : W := mkw 0x3652fda2f8a6fa2d 0x286ca5fb45f14df4 0xfe73ff03f8e7f85f 0xdffce7fe07f1cff0

def z359 : W := mkw 0x565776ec0000003e 0x00acaeedd8000000 0x5e03fffc00000001 0xdebc07fff8000000

def z360 : W := mkw 0x7fffffeffd56f07f 0xe0ffffffdffaade0 0xfffffffffffff87f 0xfffffffffffffff0

def z361 : W := mkw 0x405676a40000002e 0x0080aced48000000 0x00007f0000000000 0x000000fe00000000

def z362 : W := mkw 0x0000010008005000 0x00000002001000a0 0x000000001800f85a 0x00000000003001f0

def z363 : W := mkw 0x1fa88013d7558541 0xd03f510027aeab0a 0xbffc0003ffffc7fe 0x3f7ff80007ffff8f

def z364 : W := mkw 0x0000000355500001 0xc000000006aaa000 0xa0000003fff8003e 0x0140000007fff000

def z365 : W := mkw 0x1f83a45987058530 0x903f0748b30e0b0a 0xdf83ffff8707c7ef 0xffbf07ffff0e0f8f

def z366 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x42cffffc00000001 0xfa859ffff8000000

def z367 : W := mkw 0x5fbbb47987058574 0x90bf7768f30e0b0a 0xdd33b87386070004 0x85ba6770e70c0e00

def z368 : W := mkw 0x005050b002a10e0c 0x0800a0a16005421c 0x017040f006e03e72 0x7202e081e00dc07c

def z369 : W := mkw 0x20008913ff07f501 0xb040011227fe0fea 0xa0000003ff07fffe 0x0140000007fe0fff

def z370 : W := mkw 0x5fbbb47987058574 0x90bf7768f30e0b0a 0xddb3b8ff8707c7ef 0xefbb6771ff0e0f8f

def z371 : W := mkw 0x0000010008885a80 0x04000002001110b5 0x000000000000ffc0 0x00000000000001ff

def z372 : W := mkw 0x3642ed82f886fa29 0x206c85db05f10df4 0xfe43ff83f887fe7f 0xfffc87ff07f10ffc

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x0170000006e00020 0x2002e000000dc000

def z374 : W := mkw 0x3646e786d88cdaab 0x246c8dcf0db119b5 0xdacfc78f9998fffb 0x7bb59f8f1f3331ff

def z375 : W := mkw 0x005058b377f32e0d 0xc800a0b166efe65c 0xa57078f3ffff3e7e 0xf74ae0f1e7fffe7c

def z376 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x217000f066e73e76 0x2042e001e0cdce7c

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000100c7ea 0x000000000002018f

def z378 : W := mkw 0x3f83a55bdf05d531 0xb07f074ab7be0baa 0xdb8387ff9f07c7ef 0xefb7070fff3e0f8f

def z379 : W := mkw 0x0000010008005000 0x00000002001000a0 0x02cc47001998f87b 0x7a05988e003331f0

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x27fc00007ff8003e 0x3e4ff80000fff000

def z381 : W := mkw 0x0010102000000004 0x0000202040000000 0x0530387000000000 0x840a6070e0000000

def z382 : W := mkw 0x36008902f806f001 0x206c011205f00de0 0xbe000003f807f85e 0x1f7c000007f00ff0

def z383 : W := mkw 0x0045c3dc8a8ddf9a 0x14008b87b9151bbf 0x42cfc7fc199ffffb 0xfa859f8ff8333fff

def z384 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003e6600004 0x3f7ff80007ccc000

def z385 : W := mkw 0x00008013d7558501 0xd000010027aeab0a 0xa0000003ffffc7fe 0x0140000007ffff8f

def z386 : W := mkw 0x005453a408885a8e 0x0400a8a7481110b5 0x07fc7ffc1998fffb 0xfe0ff8fff83331ff

def z387 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c19983fb0 0x3005988f1833307f

def z388 : W := mkw 0x1ff9d8fbf7f7af5d 0xd83ff3b1f7efef5e 0xfffff8ffffffffff 0xfffffff1ffffffff

def z389 : W := mkw 0x3646ef86f88efaab 0x246c8ddf0df11df5 0xfe03ff8ff807ffdf 0xdffc07ff1ff00fff

def z390 : W := mkw 0x20008902f806f001 0x2040011205f00de0 0xa2004703f807f85f 0x5b44008e07f00ff0

def z391 : W := mkw 0x362a2d0278527061 0x606c545a04f0a4e0 0x267c7f0078f83810 0x104cf8fe00f1f070

def z392 : W := mkw 0x1fec42875550004b 0xc03fd8850eaaa000 0xbffc478ffff8003f 0x7f7ff88f1ffff000

def z393 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0x6403ff006007f857 0xd6c807fe00c00ff0

def z394 : W := mkw 0x5fff7eec20a22a7e 0x08bffefdd8414454 0x7ffffffc60e03811 0xfefffffff8c1c070

def z395 : W := mkw 0x7ffffeeef006a07f 0x20fffffddde00d40 0xffffffffe0070005 0xffffffffffc00e00

def z396 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000008000000662 0x620000010000000c

def z397 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x0000008c00000780 0x000000011800000f

def z398 : W := mkw 0x567e77a408885aee 0x04acfcef481110b5 0x067c7f0018983810 0x100cf8fe00313070

def z399 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4573fffc00000001 0xf68ae7fff8000000

def z400 : W := mkw 0x5fbb346b55500075 0xc0bf7668d6aaa000 0xffffb873fff8003e 0xbfffff70e7fff000

def z401 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c18983811 0x7a05988f18313070

def z402 : W := mkw 0x0045c3dc8a8ddf9a 0x14008b87b9151bbf 0x4003c7fc0007ffc1 0xc080078ff8000fff

def z403 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5a8ffffc00000001 0xc8b51ffff8000000

def z404 : W := mkw 0x1ff850a00000004c 0x003ff0a140000000 0x1ffc78f000000000 0xfe3ff8f1e0000000

def z405 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5bff87fc00000001 0x28b7ff0ff8000000

def z406 : W := mkw 0x5ffff6fc8205857e 0x10bfffedf9040b0a 0x5ffffffc0007c7c1 0xfebffffff8000f8f

def z407 : W := mkw 0x567e77a408885aee 0x04acfcef481110b5 0x06fc7f8c1998fffb 0x7a0df8ff183331ff

def z408 : W := mkw 0x3602a402d0048021 0x206c054805a00900 0xd803800380000000 0x01b0070007000000

def z409 : W := mkw 0x0981004800000010 0x0013020090000000 0x5903807000000000 0x84b20700e0000000

def z410 : W := mkw 0x0000000355500001 0xc000000006aaa000 0xa5700003fff8003e 0x374ae00007fff000

def z411 : W := mkw 0x5fff7eec2002207e 0x00bffefdd8400440 0x7ffffffc60073857 0xfefffffff8c00e70

def z412 : W := mkw 0x49fdd2fd8705855e 0x9093fba5fb0e0b0a 0xd9ff80ff8707c7ef 0xefb3ff01ff0e0f8f

def z413 : W := mkw 0x1fa8000000000040 0x003f500000000000 0x1a8c000000000000 0x0835180000000000

def z414 : W := mkw 0x1faa240000000060 0x003f544800000000 0x5fffff0000000001 0xfebffffe00000000

def z415 : W := mkw 0x3646ef86f88efaab 0x246c8ddf0df11df5 0xfe4fff03f89ff85f 0xdffc9ffe07f13ff0

def z416 : W := mkw 0x0980000105000000 0x80130000020a0000 0x9980008f8700c7ef 0x6f3300011f0e018f

def z417 : W := mkw 0x09d1d8f9a7a7af1c 0x9813a3b1f34f4f5e 0xfd73f8f3e6e73e76 0xf7fae7f1e7cdce7c

def z418 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x0200478c1800ffdb 0x5a04008f183001ff

def z419 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc47001998383a 0x3a05988e00333070

def z420 : W := mkw 0x0044c3958f8ddf8a 0x940089872b1f1bbf 0x82cc478f9f9fffff 0x7b05988f1f3f3fff

def z421 : W := mkw 0x1fa8080375522041 0xc03f501006eaa440 0xbffc7803ffff387e 0xff7ff8f007fffe70

def z422 : W := mkw 0x3612bc32f227a425 0x286c257865e44f48 0xfd33b873e6670004 0x85fa6770e7ccce00

def z423 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xba8c0003fff8003e 0x0975180007fff000

def z424 : W := mkw 0x0000801187058500 0x90000100230e0b0a 0xd80380038707c7ef 0xcfb00700070e0f8f

def z425 : W := mkw 0x3ffafdb3fff7fe6d 0xe87ff5fb67ffeffc 0xfffffff3fffffe7f 0xffffffffe7fffffc

def z426 : W := mkw 0x0981005802010410 0x00130200b0040208 0x598380fc06070667 0xeeb30701f80c0e0c

def z427 : W := mkw 0x09a9805987558550 0xd0135300b30eab0a 0xd9ff80ff87ffc7ef 0xefb3ff01ff0fff8f

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x2400000060000016 0x1648000000c00000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x0570000000000000 0x360ae00000000000

def z430 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x024c478c1898ffd1 0x5004988f183131ff

def z431 : W := mkw 0x5faf264f55500073 0xc0bf5e4c9eaaa000 0xda8f870f99180009 0x09b51f0e1f323000

def z432 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257038f066e70624 0xa44ae071e0cdce0c

def z433 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbf300003fe60001e 0x1f7e600007fcc000

def z434 : W := mkw 0x5fafa65d87058572 0x90bf5f4cbb0e0b0a 0xdb8f87ff8707c7ef 0xefb71f0fff0e0f8f

def z435 : W := mkw 0x0004030408085082 0x04000806081010a1 0x020c070018180000 0x0004180e00303000

def z436 : W := mkw 0x1628000250500041 0x402c500004a0a000 0x26fc000079f8003a 0x3a4df80000f3f000

def z437 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd883800f8707c7ef 0x09b107001f0e0f8f

def z438 : W := mkw 0x005452a40000000e 0x0000a8a548000000 0x07fc7ffc00000001 0xfe0ff8fff8000000

def z439 : W := mkw 0x3612bd32fa27f425 0x286c257a65f44fe8 0xff33ff73fe67f85f 0xdffe67fee7fccff0

def z440 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbefc0003f9f80018 0x197df80007f3f000

def z441 : W := mkw 0x0000080020a22a00 0x0800001000414454 0x2000000060e03810 0x0040000000c1c070

def z442 : W := mkw 0x20022d0028027020 0x2040045a005004e0 0x00007f0000003800 0x000000fe00000070

def z443 : W := mkw 0x004443875dd85a8b 0xc40088870ebbb0b5 0xa2cc478ffff8ffff 0x7b45988f1ffff1ff

def z444 : W := mkw 0x0985835d8f0dd592 0x94130b06bb1e1bab 0xdb8f87ff9f1fc7ef 0xefb71f0fff3e3f8f

def z445 : W := mkw 0x1fec43875dd85acb 0xc43fd8870ebbb0b5 0x9acc478f9998fffb 0x7b35988f1f3331ff

def z446 : W := mkw 0x0000801082058400 0x0000010021040b08 0xd90380f38607c66f 0xefb20701e70c0f8c

def z447 : W := mkw 0x3602ad12faa7fe21 0x286c055a25f54ffc 0xfe03ff03fee7fe7f 0xdffc07fe07fdcffc

def z448 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x004c000000980000 0x0000980000013000

def z449 : W := mkw 0x20008902f806f001 0x2040011205f00de0 0xf8038003f807f85f 0xcff0070007f00ff0

def z450 : W := mkw 0x0000001002010400 0x0000000020040208 0x0100007006070004 0x84020000e00c0e00

def z451 : W := mkw 0x3f83ac5bf707a531 0xb07f0758b7ee0f4a 0xfd03b873e6070004 0x85fa0770e7cc0e00

def z452 : W := mkw 0x36527db27aa37e2d 0x286ca4fb64f546fc 0x27707ff07ee73e76 0xf64ee0ffe0fdce7c

def z453 : W := mkw 0x767effa6f806f06f 0x20ecfdff4df00de0 0xfe7fff03f807f85f 0xdffcfffe07f00ff0

def z454 : W := mkw 0x0000800185048100 0x90000100030a0902 0x800000038100c188 0x0100000007020183

def z455 : W := mkw 0x1fa9005b57510551 0xd03f5200b6aea20a 0xbffc00fffff807be 0x3f7ff801fffff00f

def z456 : W := mkw 0x3f83ad4af806f031 0x207f075a95f00de0 0xff83fffff807f85f 0xffff07fffff00ff0

def z457 : W := mkw 0x3f83ac5bf707a531 0xb07f0758b7ee0f4a 0xfd83b8ffe707c7ef 0xeffb0771ffce0f8f

def z458 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xa6007f03f807f85e 0x114c00fe07f00ff0

def z459 : W := mkw 0x0000080020022000 0x0000001000400440 0x2400380060070004 0x8448007000c00e00

def z460 : W := mkw 0x0010183022232404 0x0800203060444648 0x2530787066673856 0xd64a60f0e0ccce70

def z461 : W := mkw 0x0981005907010510 0x90130200b20e020a 0x018000fc0700c7eb 0x6a030001f80e018f

def z462 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x057078f000073e40 0xf60ae0f1e0000e7c

def z463 : W := mkw 0x0981004800000010 0x0013020090000000 0x598380fc0100c7eb 0xeeb30701f802018f

def z464 : W := mkw 0x49fd52ec0000005e 0x0093faa5d8000000 0x05fc78fc00000000 0xf60bf8f1f8000000

def z465 : W := mkw 0x0000010008005000 0x00000002001000a0 0x0200470018003810 0x1004008e00300070

def z466 : W := mkw 0x3f83ad5bff07f531 0xb07f075ab7fe0fea 0xff03ff73fe07f85f 0xdffe07fee7fc0ff0

def z467 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x024c47001898f85b 0x5a04988e003131f0

def z468 : W := mkw 0x1fb8183377732445 0xc83f703066eee648 0xbd303873e6670004 0x857a6070e7ccce00

def z469 : W := mkw 0x2002ac00a006a020 0x2040055801400d40 0x4003b80000070000 0x8080077000000e00

def z470 : W := mkw 0x5fff7eff77f32e7f 0xc8bffefdfeefe65c 0xffffffffffff3e7f 0xfffffffffffffe7c

def z471 : W := mkw 0x1fedc3dfdfdddfdb 0xd43fdb87bfbfbbbf 0xffffc7ffffffffff 0xffffff8fffffffff

def z472 : W := mkw 0x00444b942aab7e8a 0x0c008897285556fd 0x22cc478c7fffffff 0x7a45988f18ffffff

def z473 : W := mkw 0x16008002d0048001 0x002c010005a00900 0xfe038003f807c05f 0xdffc070007f00f80

def z474 : W := mkw 0x0001804880048110 0x1000030091000902 0x4003800c0000c181 0x0080070018000183

def z475 : W := mkw 0x0040408000800a08 0x0000808100010014 0x0040400000803810 0x1000808000010070

def z476 : W := mkw 0x0000090028027000 0x00000012005004e0 0x26007f007807f85f 0xde4c00fe00f00ff0

def z477 : W := mkw 0x00545ab422a32e0e 0x0800a8b56845465c 0x27fc7ffc66e73e77 0xfe4ff8fff8cdce7c

def z478 : W := mkw 0x3602ad02f88efaa1 0x246c055a05f11df5 0xfe03ff03f99fffff 0xdffc07fe07f33fff

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000001998003a 0x0000000000333000

def z480 : W := mkw 0x49fd52fd0701055e 0x9093faa5fa0e020a 0x01fc00fc070007a0 0x2003f801f80e000f

def z481 : W := mkw 0x1600000250000001 0x002c000004a00000 0xbecc0003f998003e 0x3f7d980007f33000

def z482 : W := mkw 0x0981804985048110 0x90130300930a0902 0xd98380ff8100c189 0xefb30701ff020183

def z483 : W := mkw 0x36466f86788a7aab 0x246c8cdf0cf114f5 0x264c7f0078983810 0x104c98fe00f13070

def z484 : W := mkw 0x3fabad5bff57f571 0xf07f575ab7feafea 0xffffffffffffffff 0xffffffffffffffff

def z485 : W := mkw 0x16022c0020022020 0x002c045800400440 0x7e03ff0060073857 0xdefc07fe00c00e70

def z486 : W := mkw 0x005058a020a22a0c 0x0800a0b140414454 0x257078f060e03810 0xf64ae0f1e0c1c070

def z487 : W := mkw 0x5ffb74e80000007c 0x00bff6e9d0000000 0x5d73f8f000000000 0xf6bae7f1e0000000

def z488 : W := mkw 0x09d150f907a10f1c 0x9813a2a1f20f421e 0x01f000fc07e007a0 0x2003e001f80fc00f

def z489 : W := mkw 0x0981804985048110 0x90130300930a0902 0xd983800f8700c1af 0x2fb307001f0e0183

def z490 : W := mkw 0x36466f86788a7aab 0x246c8cdf0cf114f5 0x26cc7f8c7998fffb 0x7a4d98ff18f331ff

def z491 : W := mkw 0x405777ec08885abe 0x0480aeefd81110b5 0x42cffffc1998fffb 0xfa859ffff83331ff

def z492 : W := mkw 0x3fa88903fd56f041 0xe07f511207faade0 0xbffc0003fffff87e 0x3f7ff80007fffff0

def z493 : W := mkw 0x0000010008885a80 0x04000002001110b5 0x0000000018983810 0x0000000000313070

def z494 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0x418380fc0707c7e1 0xe0830701f80e0f8f

def z495 : W := mkw 0x167858a270f22a4d 0x482cf0b144e1e454 0x267c780078f83810 0x104cf8f000f1f070

def z496 : W := mkw 0x5fff7ffc2aab7efe 0x0cbffefff85556fd 0x7ffffffc7fffffff 0xfefffffff8ffffff

def z497 : W := mkw 0x5ffff7fd8f8ddffe 0x94bfffeffb1f1bbf 0xdfffffff9f9fffff 0xffbfffffff3f3fff

def z498 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x004078f000873e72 0xf20080f1e0010e7c

def z499 : W := mkw 0x0004020400080082 0x0400080408001001 0x008c000c01180180 0x0001180018023003

def z500 : W := mkw 0x09d150e80000001c 0x0013a2a1d0000000 0x5df3f8fc00000001 0xfebbe7f1f8000000

def z501 : W := mkw 0x3f83a54bdd04d131 0xb07f074a97ba09a2 0xda83870f9900c189 0x09b5070e1f320183

def z502 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x017078f006e73e60 0xe002e0f1e00dce7c

def z503 : W := mkw 0x5ffffefda7a7af7e 0x98bffffdfb4f4f5e 0xffffffffe7e7ffff 0xffffffffffcfcfff

def z504 : W := mkw 0x1ff850b357f10e4d 0xc83ff0a166afe21c 0xbffc00f3fff8063e 0x3f7ff801e7fff00c

def z505 : W := mkw 0x5ffff6ec8004807e 0x00bfffedd9000900 0xdfffffff8007c04f 0xffbfffffff000f80

def z506 : W := mkw 0x0000000000880a80 0x0400000000011015 0x00000000019807a0 0x000000000003300f

def z507 : W := mkw 0x000001035dd85a81 0xc400000206bbb0b5 0xa0000003fff8fffe 0x0140000007fff1ff

def z508 : W := mkw 0x0000001002010400 0x0000000020040208 0x000000f000070640 0xc0000001e0000e0c

def z509 : W := mkw 0x0000010008085080 0x04000002001010a1 0x000000001918c188 0x0000000000323183

def z510 : W := mkw 0x1fa801035dd85ac1 0xc43f500206bbb0b5 0xbffc0003fff8fffe 0x3f7ff80007fff1ff

def z511 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x0040478c0080fff3 0x7200808f180101ff

def z512 : W := mkw 0x005452b402a90e8e 0x0c00a8a56805521d 0x01fc00fc07f807a0 0x2003f801f80ff00f

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000038000000e 0x0f30000007000000

def z514 : W := mkw 0x3602ac02f006a021 0x206c055805e00d40 0xfc03f803e0073856 0xd7f807f007c00e70

def z515 : W := mkw 0x567e7eb422a32e6e 0x08acfcfd6845465c 0x277c7ff066e73e76 0xf64ef8ffe0cdce7c

def z516 : W := mkw 0x1f81805bd7058511 0x903f0300b7ae0b0a 0xff8380ffff07c7ff 0xffff0701fffe0f8f

def z517 : W := mkw 0x0000000105500000 0xc0000000020aa000 0x0000000007f80020 0x00000000000ff000

def z518 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380f386070666 0xe7b20701e70c0e0c

def z519 : W := mkw 0x0000000355500001 0xc000000006aaa000 0xa2cc0003fff8003e 0x3b45980007fff000

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000066e00036 0x0040000000cdc000

def z521 : W := mkw 0x3602a502d804d021 0x206c054a05b009a0 0xfe038703f800c01f 0x1ffc070e07f00180

def z522 : W := mkw 0x0004030408085082 0x04000806081010a1 0x028c470c1918f9db 0x5a05188e183231f3

def z523 : W := mkw 0x3603ad5afa07f531 0x306c075ab5f40fea 0xfe03fffff807ffdf 0xdffc07fffff00fff

def z524 : W := mkw 0x5ffe76a75550006f 0xc0bffced4eaaa000 0xbffc7f03fff8003e 0x3f7ff8fe07fff000

def z525 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x00cc478c0198ffe1 0x6001988f180331ff

def z526 : W := mkw 0x0981804880048010 0x0013030091000900 0xd98380ff8007c04f 0xefb30701ff000f80

def z527 : W := mkw 0x0040408000000008 0x0000808100000000 0x0040408000000000 0x7200808100000000

def z528 : W := mkw 0x20008102d804d001 0x2040010205b009a0 0x800000039800c008 0x0100000007300180

def z529 : W := mkw 0x0000010008885a80 0x04000002001110b5 0x020047001998fffb 0x5a04008e003331ff

def z530 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbd700003e6e00036 0x377ae00007cdc000

def z531 : W := mkw 0x3606a706d80cd0a3 0x246c0d4e0db019a1 0xda8f870f9918c189 0x09b51f0e1f323183

def z532 : W := mkw 0x0000080020022000 0x0000001000400440 0x2400780060003810 0x104800f000c00070

def z533 : W := mkw 0x3fd3fdfbffa7ff3d 0xb87fa7fbf7ff4ffe 0xfff3ffffffe7ffff 0xffffe7ffffffcfff

def z534 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x9acc00039998003a 0x3b35980007333000

def z535 : W := mkw 0x3602a502d804d021 0x206c054a05b009a0 0xde03ff039800c009 0xdfbc07fe07300180

def z536 : W := mkw 0x1644438658885a8b 0x042c88870cb110b5 0xbecc478ff998ffff 0x7f7d988f1ff331ff

def z537 : W := mkw 0x49d7f6fd8705853e 0x9093afedfb0e0b0a 0xd983ffff8707c7ef 0xefb307ffff0e0f8f

def z538 : W := mkw 0x00545bb42aab7e8e 0x0c00a8b7685556fd 0x277c7ff07eff3e76 0xf64ef8ffe0fdfe7c

def z539 : W := mkw 0x0981005907010510 0x90130200b20e020a 0x998000ff870007ae 0x2f330001ff0e000f

def z540 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbdb00003e760002e 0x2f7b600007cec000

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x02cc008c1998c7fb 0x7a0598011833318f

def z542 : W := mkw 0x1fac03075d5850c3 0xc43f58060ebab0a1 0xbffc070ffff8c1bf 0x3f7ff80e1ffff183

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x02cc000000000000 0x3a05980000000000

def z544 : W := mkw 0x7fffffeca806f07e 0x20ffffffd9500de0 0x5ffffffc0007f841 0xfebffffff8000ff0

def z545 : W := mkw 0x20008900a806f000 0x2040011201500de0 0x000000000007f840 0x0000000000000ff0

def z546 : W := mkw 0x3602250258005021 0x206c044a04b000a0 0x0200070018000000 0x0004000e00300000

def z547 : W := mkw 0x09c543dd0f895f9a 0x94138a87ba1f12bf 0x03cc47fc1f98fffb 0x7a07988ff83f31ff

def z548 : W := mkw 0x1628000250500041 0x402c500004a0a000 0x2430000060600000 0x0048600000c0c000

def z549 : W := mkw 0x5fff76fc02a10e7e 0x08bffeedf805421c 0x5ffffffc06e00621 0xfebffffff80dc00c

def z550 : W := mkw 0x0980800185048000 0x80130100030a0900 0xd98380038707c06f 0xefb30700070e0f80

def z551 : W := mkw 0x49ad024c00000052 0x00935a0498000000 0x008c000c00000000 0x0001180018000000

def z552 : W := mkw 0x0001805987058510 0x90000300b30e0b0a 0xc00380ff8707c7ef 0xc1800701ff0e0f8f

def z553 : W := mkw 0x3656ffb6faaffeaf 0x2c6cadff6df55ffd 0xffffffffffffffff 0xffffffffffffffff

def z554 : W := mkw 0x3646ef86f806f02b 0x206c8ddf0df00de0 0xfecfff8ff807f85f 0xfffd9fff1ff00ff0

def z555 : W := mkw 0x0000000250500001 0x4000000004a0a000 0x2000000078f80010 0x0040000000f1f000

def z556 : W := mkw 0x005050b00201040c 0x0000a0a160040208 0x057078f006070666 0xf60ae0f1e00c0e0c

def z557 : W := mkw 0x09c542cc0000001a 0x00138a8598000000 0x5bcfc7fc00000001 0xfeb79f8ff8000000

def z558 : W := mkw 0x1fa9805bd7558551 0xd03f5300b7aeab0a 0xfdb380ffe767c7ef 0xeffb6701ffcecf8f

def z559 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380738607c04f 0xcfb20700e70c0f80

def z560 : W := mkw 0x00545bb42aab7e8e 0x0c00a8b7685556fd 0x25707ffc66e7fff7 0xf64ae0fff8cdcfff

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000070046 0xc600000000000e00

def z562 : W := mkw 0x005058a020a22a0c 0x0800a0b140414454 0x2470780060e73856 0xd648e0f000c1ce70

def z563 : W := mkw 0x1600000250000001 0x002c000004a00000 0xbf700003fee0003e 0x3f7ee00007fdc000

def z564 : W := mkw 0x5fafa64d85048172 0x90bf5f4c9b0a0902 0xda8f870f8100c189 0x09b51f0e1f020183

def z565 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5fbfbf7c00000001 0x8cbf7f7ef8000000

def z566 : W := mkw 0x0000801187058500 0x90000100230e0b0a 0x8080008f8707c7ef 0x6b0100011f0e0f8f

def z567 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc078c1998c7a9 0x2805980f1833318f

def z568 : W := mkw 0x1fb8183377732445 0xc83f703066eee648 0xbffc3873ffff003e 0xbf7ff870e7fffe00

def z569 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff870707a4 0xa5b30701ff0e0e0f

def z570 : W := mkw 0x5fff76fc0201047e 0x00bffeedf8040208 0x5ffffffc06070667 0xfebffffff80c0e0c

def z571 : W := mkw 0x005050a00000000c 0x0000a0a140000000 0x257078f066e00036 0xf64ae0f1e0cdc000

def z572 : W := mkw 0x0981805882058510 0x10130300b1040b0a 0x598380fc0007c7c1 0xeeb30701f8000f8f

def z573 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5fffb87000000000 0xbebfff70e0000000

def z574 : W := mkw 0x3f82ad03fd06f021 0xa07f055a07fa0de0 0xff83ff03ff07f87f 0xffff07fe07fe0ff0

def z575 : W := mkw 0x3602ad00a806f020 0x206c055a01500de0 0x5e03ff000007f841 0xdebc07fe00000ff0

def z576 : W := mkw 0x0981804985048110 0x90130300930a0902 0xd883800f8107c1cf 0xcfb107001f020f83

def z577 : W := mkw 0x5faf264f55500073 0xc0bf5e4c9eaaa000 0xffff870ffff8003f 0x3fffff0e1ffff000

def z578 : W := mkw 0x0051d8f8a2a7af1c 0x1800a3b1f1454f5e 0x6573f8fc66e7fff7 0xf6cae7f1f8cdcfff

def z579 : W := mkw 0x1fa9804bd5548151 0xd03f530097aaa902 0xffff800ffff8c1bf 0x3fffff001ffff183

def z580 : W := mkw 0x00545bb42aab7e8e 0x0c00a8b7685556fd 0x02cc7ffc199ffffb 0xfa0598fff8333fff

def z581 : W := mkw 0x5fab244800000070 0x00bf564890000000 0x5803800000000000 0x00b0070000000000

def z582 : W := mkw 0x36527da278a27a2d 0x286ca4fb44f144f4 0x26707f0078e03810 0x104ce0fe00f1c070

def z583 : W := mkw 0x1600000000000000 0x002c000000000000 0x1e00000000000000 0x1e3c000000000000

def z584 : W := mkw 0x2981895bff07f511 0xb0530312b7fe0fea 0xf98380ffff07ffff 0xeff30701fffe0fff

def z585 : W := mkw 0x005050a00000000c 0x0000a0a140000000 0x0470780000000000 0x1008e0f000000000

def z586 : W := mkw 0x3fc7efdfff8fffbb 0xb47f8fdfbfff1fff 0xffcfffffff9fffff 0xffff9fffffff3fff

def z587 : W := mkw 0x0981004800000010 0x0013020090000000 0x5883800c00000001 0x08b1070018000000

def z588 : W := mkw 0x2044cb86f88efa8b 0x244089970df11df5 0xa2cc478ff99fffff 0x7b45988f1ff33fff

def z589 : W := mkw 0x005058a020a22a0c 0x0800a0b140414454 0x2470788060e03e72 0x7248e0f100c1c07c

def z590 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x02cc008c199807ba 0x3a0598011833300f

def z591 : W := mkw 0x1646678408885aaa 0x042c8ccf081110b5 0x5ecfff8c1998fffb 0xfebd9fff183331ff

def z592 : W := mkw 0x1600000355500001 0xc02c000006aaa000 0xbe000003fff8003e 0x1f7c000007fff000

def z593 : W := mkw 0x1602240000000020 0x002c044800000000 0x06007f0000000000 0x100c00fe00000000

def z594 : W := mkw 0x2052fdb0aaa7fe2c 0x2840a5fb61554ffc 0x6573fff066e7fe77 0xf6cae7ffe0cdcffc

def z595 : W := mkw 0x0010183022232404 0x0800203060444648 0x2570387066e70036 0xb64ae070e0cdce00

def z596 : W := mkw 0x1600000250000001 0x002c000004a00000 0xbc000003e0000004 0x0578000007c00000

def z597 : W := mkw 0x0980001107010400 0x80130000220e0208 0x998000f38707066e 0xef330001e70e0e0c

def z598 : W := mkw 0x09d1d8f9a7a7af1c 0x9813a3b1f34f4f5e 0xd983f8ff8707ffef 0xefb307f1ff0e0fff

def z599 : W := mkw 0x1fa9805bd7558551 0xd03f5300b7aeab0a 0xfd338073e6670004 0x85fa6700e7ccce00

def z600 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x07fc7ffc00000000 0x300ff8fff8000000

def z601 : W := mkw 0x005050b002a10e0c 0x0800a0a16005421c 0x017000f006e70666 0xe602e001e00dce0c

def z602 : W := mkw 0x165058b272a32e0d 0x082ca0b164e5465c 0xbf7078f3fee73e7e 0xff7ee0f1e7fdce7c

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x5803800000000001 0xceb0070000000000

def z604 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x024c47001998fffa 0x1004988e003331ff

def z605 : W := mkw 0x5fef66cc0000007a 0x00bfdecd98000000 0x5acfc78c00000001 0x7ab59f8f18000000

def z606 : W := mkw 0x0000800080048000 0x0000010001000900 0xd803800380070004 0x85b0070007000e00

def z607 : W := mkw 0x0000010008005000 0x00000002001000a0 0x000047000000f841 0x4000008e000001f0

def z608 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd983807f8707c18d 0x8db30700ff0e0f83

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x2530000066600004 0x044a600000ccc000

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x2470000060e00010 0x1048e00000c1c000

def z611 : W := mkw 0x5ffd52ef5550005f 0xc0bffaa5deaaa000 0xbffc00fffff8003e 0x3f7ff801fffff000

def z612 : W := mkw 0x1fac03075d5850c3 0xc43f58060ebab0a1 0x9a8c070f9918c189 0x0935180e1f323183

def z613 : W := mkw 0x5ffb7cf822a32e7c 0x08bff6f9f045465c 0x7d73f8f066e73e76 0xf6fae7f1e0cdce7c

def z614 : W := mkw 0x0980000105000000 0x80130000020a0000 0xbdf00003e7e0003e 0x3f7be00007cfc000

def z615 : W := mkw 0x09f850b107f10e4c 0xc813f0a1620fe21c 0x01fc00f007f80620 0x2003f801e00ff00c

def z616 : W := mkw 0x3652fdb2faa7fe2d 0x286ca5fb65f54ffc 0xfe03fff3f807fe5f 0xdffc07ffe7f00ffc

def z617 : W := mkw 0x09ec43850dd85aca 0xc413d8870a1bb0b5 0x03fc478c1ff8fffb 0x7a07f88f183ff1ff

def z618 : W := mkw 0x36022c0270022021 0x206c045804e00440 0x2400380060000000 0x0048007000c00000

def z619 : W := mkw 0x0000801187058500 0x90000100230e0b0a 0x810000f38707c7ee 0xe7020001e70e0f8f

def z620 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x240078f060073e56 0xd64800f1e0c00e7c

def z621 : W := mkw 0x5fff76ec00880afe 0x04bffeedd8011015 0x5ffffffc019807a1 0xfebffffff803300f

def z622 : W := mkw 0x1fa9004800000050 0x003f520090000000 0x5fff80fc00000001 0xfebfff01f8000000

def z623 : W := mkw 0x1600010258005001 0x002c000204b000a0 0xbe004703f800f85f 0x5f7c008e07f001f0

def z624 : W := mkw 0x000081008804d000 0x00000102011009a0 0xda03c7039807f85f 0xdfb4078e07300ff0

def z625 : W := mkw 0x005050a000a00a0c 0x0800a0a140014014 0x0070000000e00000 0x0000e0000001c000

def z626 : W := mkw 0x0000001002010400 0x0000000020040208 0x0000000006070666 0x00000000000c0e0c

def z627 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x024c478018983e72 0x7204988f0031307c

def z628 : W := mkw 0x7fafaf4ef806f073 0x20ff5f5e9df00de0 0xfe8fff0ff807f85f 0xdffd1ffe1ff00ff0

def z629 : W := mkw 0x0010103002210404 0x0800202060044208 0x0130007006600000 0x00026000e00cc000

def z630 : W := mkw 0x20008902f806f001 0x2040011205f00de0 0xa4007803f807f85e 0xd74800f007f00ff0

def z631 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5dffb8fc00000000 0xa4bbff71f8000000

def z632 : W := mkw 0x3602ad13ff07f521 0xb06c055a27fe0fea 0xfe03ff03ff07ffff 0xdffc07fe07fe0fff

def z633 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0x818000ff8707c7ee 0x21030001ff0e0f8f

def z634 : W := mkw 0x0010182020222004 0x0800203040404440 0x2430380060600000 0x0048607000c0c000

def z635 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0x408380fc0107c7eb 0xea810701f8020f8f

def z636 : W := mkw 0x1fa8081377f32e41 0xc83f501026efe65c 0xbffc0003ffff3e7e 0x3f7ff80007fffe7c

def z637 : W := mkw 0x0050d8b0a2a7ae0c 0x0800a1b161454f5c 0xfd73f8f3e6e7fe7f 0xfffae7f1e7cdcffc

def z638 : W := mkw 0x0004020400000002 0x0000080408000000 0x028c070c00000001 0x0805180e18000000

def z639 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x9b8c00039f18002e 0x2f371800073e3000

def z640 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0x410380fc0607c7e7 0xe6820701f80c0f8f

def z641 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x9800000380000000 0x0130000007000000

def z642 : W := mkw 0x0040409002810e08 0x000080812005021c 0x014040f006873e76 0xf6028081e00d0e7c

def z643 : W := mkw 0x0985834d8d0cd192 0x94130b069b1a19a3 0xda8f870f9918c189 0x09b51f0e1f323183

def z644 : W := mkw 0x567e7ea420a22a6e 0x08acfcfd48414454 0x267c7f0060e03810 0x104cf8fe00c1c070

def z645 : W := mkw 0x1fa9804bd5548151 0xd03f530097aaa902 0xda8f800f9918c189 0x09b51f001f323183

def z646 : W := mkw 0x7fff7fee7802707f 0x20fffeffdcf004e0 0x7ffffffc78003811 0xfefffffff8f00070

def z647 : W := mkw 0x3602ad03fd56f021 0xe06c055a07faade0 0xfe03ff03fffff87f 0xdffc07fe07fffff0

def z648 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbdfc0003e7f80024 0x257bf80007cff000

def z649 : W := mkw 0x0980000105000000 0x80130000020a0000 0x9bcc00039f98003e 0x3f379800073f3000

def z650 : W := mkw 0x405777ec08885abe 0x0480aeefd81110b5 0x4003fffc0000ffc1 0xc08007fff80001ff

def z651 : W := mkw 0x0000010008005000 0x00000002001000a0 0x020007001800c009 0x0804000e00300180

def z652 : W := mkw 0x1628000250500041 0x402c500004a0a000 0x020c000018180000 0x0004180000303000

def z653 : W := mkw 0x5ffff6fd8705857e 0x90bfffedfb0e0b0a 0xdfffffff86070005 0xffbfffffff0c0e00

def z654 : W := mkw 0x0040488020822a08 0x0000809100410454 0x2440788060873e76 0xf64880f100c10e7c

def z655 : W := mkw 0x1602240000000020 0x002c044800000000 0x5c03b80000000000 0x84b8077000000000

def z656 : W := mkw 0x0001005802010510 0x10000200b004020a 0x000000fc00000780 0x00000001f800000f

def z657 : W := mkw 0x0000081022a32e00 0x080000102045465c 0x2400780066e73e76 0xd64800f000cdce7c

def z658 : W := mkw 0x36022d0278027021 0x206c045a04f004e0 0x26007f0078073856 0xd64c00fe00f00e70

def z659 : W := mkw 0x1fa8000250500041 0x403f500004a0a000 0x3ffc000078f80010 0x3e7ff80000f1f000

def z660 : W := mkw 0x1fec42840000004a 0x003fd88508000000 0x1ffc478c00000001 0x7e3ff88f18000000

def z661 : W := mkw 0x0004030408085082 0x04000806081010a1 0x02cc070c1998c1bb 0x3a05980e18333183

def z662 : W := mkw 0x0000080020022000 0x0000001000400440 0x0000780000073840 0xc00000f000000e70

def z663 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x0080478c0100ffeb 0x6a01008f180201ff

def z664 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x200078f066e73e76 0xc04000f1e0cdce7c

def z665 : W := mkw 0x3602a502d804d021 0x206c054a05b009a0 0xda03c7039800f85b 0x5bb4078e073001f0

def z666 : W := mkw 0x3faaad03fd56f061 0xe07f555a07faade0 0xff33ff03fe67f85f 0xdffe67fe07fccff0

def z667 : W := mkw 0x5fff7efc22a32e7e 0x08bffefdf845465c 0x5ffffffc00073e41 0xfebffffff8000e7c

def z668 : W := mkw 0x5fff77ec080850fe 0x04bffeefd81010a1 0x5ffffffc1918c189 0xfebffffff8323183

def z669 : W := mkw 0x2052fdb0aaa7fe2c 0x2840a5fb61554ffc 0x4003fff00007fe41 0xc08007ffe0000ffc

def z670 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0x9ffc000399180008 0x3f3ff80007323000

def z671 : W := mkw 0x3faaad02f806f061 0x207f555a05f00de0 0xffffff03f807f85f 0xfffffffe07f00ff0

def z672 : W := mkw 0x005059b02aab7e8c 0x0c00a0b3605556fd 0x257078f07ffffffe 0xf64ae0f1e0ffffff

def z673 : W := mkw 0x5ffff6ed8504817e 0x90bfffeddb0a0902 0xdfffffff8100c189 0xffbfffffff020183

def z674 : W := mkw 0x09c542dd07890f9a 0x94138a85ba0f121f 0x01cc00fc079807a0 0x20039801f80f300f

def z675 : W := mkw 0x004442840000000a 0x0000888508000000 0x00cc008c00000000 0x2001980118000000

def z676 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfc03b803f807f85e 0x85f8077007f00ff0

def z677 : W := mkw 0x1fec428755d80acb 0xc43fd8850eabb015 0xbffc008ffff807be 0x3f7ff8011ffff00f

def z678 : W := mkw 0x3602a502d804d021 0x206c054a05b009a0 0xda0387039807c04f 0xcfb4070e07300f80

def z679 : W := mkw 0x0040408000800a08 0x0000808100010014 0x0040008000800620 0x200080010001000c

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000001800001a 0x1a04000000300000

def z681 : W := mkw 0x0981804985048110 0x90130300930a0902 0xd803800380000000 0x01b0070007000000

def z682 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380738707002e 0xafb30700e70e0e00

def z683 : W := mkw 0x0000081377f32e01 0xc800001026efe65c 0xa0000003ffff3e7e 0x0140000007fffe7c

def z684 : W := mkw 0x567e76a65050006f 0x40acfced4ca0a000 0x267c7f0078f80010 0x104cf8fe00f1f000

def z685 : W := mkw 0x1602250008005020 0x002c044a001000a0 0x5e03ff001800f85b 0xdebc07fe003001f0

def z686 : W := mkw 0x1600000250000001 0x002c000004a00000 0x9a00000398000008 0x0934000007300000

def z687 : W := mkw 0x0981005907010510 0x90130200b20e020a 0x018000fc070707e6 0xe6030001f80e0e0f

def z688 : W := mkw 0x36022d0278027021 0x206c045a04f004e0 0xbe007f03f800381e 0x1f7c00fe07f00070

def z689 : W := mkw 0x2002ad02f806f021 0x2040055a05f00de0 0xe003ff03f807f85f 0xc1c007fe07f00ff0

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x028c000019180008 0x0805180000323000

def z691 : W := mkw 0x1628000250500041 0x402c500004a0a000 0x277c00007ef80036 0x364ef80000fdf000

def z692 : W := mkw 0x005050b002a10e0c 0x0800a0a16005421c 0x000000f000000600 0x00000001e000000c

def z693 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0x6603ff007807f851 0xd0cc07fe00f00ff0

def z694 : W := mkw 0x0040408000800a08 0x0000808100010014 0x0000408000003e40 0x400000810000007c

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x024c000018980010 0x1004980000313000

def z696 : W := mkw 0x00008800a006a000 0x0000011001400d40 0xfc03f803e007f85f 0xdff807f007c00ff0

def z697 : W := mkw 0x1fa8000000000040 0x003f500000000000 0x1d30000000000000 0x043a600000000000

def z698 : W := mkw 0x3faaad03fd56f061 0xe07f555a07faade0 0xfe8fff03f91ff85f 0xdffd1ffe07f23ff0

def z699 : W := mkw 0x1fec438408885aca 0x043fd887081110b5 0x1ffc478c1998fffb 0x7e3ff88f183331ff

def z700 : W := mkw 0x40577efc22a32e3e 0x0880aefdf845465c 0x4003fffc00073e41 0xc08007fff8000e7c

def z701 : W := mkw 0x5ffe76a40000006e 0x00bffced48000000 0x1ffc7f0000000000 0x3e3ff8fe00000000

def z702 : W := mkw 0x0000081022032400 0x0000001020440648 0x250078f066073e76 0xf64a00f1e0cc0e7c

def z703 : W := mkw 0x00545ba428aa7a8e 0x0c00a8b7485154f5 0x267c7f0078f83810 0x104cf8fe00f1f070

def z704 : W := mkw 0x1fa9805bd7558551 0xd03f5300b7aeab0a 0xffff8073ffff003e 0xbfffff00e7fffe00

def z705 : W := mkw 0x0044428400880a8a 0x0400888508011015 0x00cc408c01983ff2 0x720198811803307f

def z706 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x2470780066e73e76 0x1048e0f000cdce7c

def z707 : W := mkw 0x20008912fa07f501 0x3040011225f40fea 0xa0000003f807ffde 0x0140000007f00fff

def z708 : W := mkw 0x405776ec00800a3e 0x0080aeedd8010014 0x4043fffc00803e73 0xf28087fff801007c

def z709 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc010007a1 0xfebffffff802000f

def z710 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x25fc78f067ff3e76 0xf64bf8f1e0cffe7c

def z711 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe83ff8ff807f85f 0xfffd07ff1ff00ff0

def z712 : W := mkw 0x3646ee86f08eaaab 0x246c8ddd0de11d55 0xfccfb88fe19f07a4 0xa5f99f711fc33e0f

def z713 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfffffffff9f80019 0xfffffffffff3f000

def z714 : W := mkw 0x567ef6b58705856e 0x90acfded6b0e0b0a 0x867c7f038707c7ee 0x110cf8fe070e0f8f

def z715 : W := mkw 0x09c5c3dd8f8ddf9a 0x94138b87bb1f1bbf 0xdb4fc7739e9f3814 0x95b69f8ee73d3e70

def z716 : W := mkw 0x0010183022a32e04 0x080020306045465c 0x2530387066673e44 0x844a6070e0ccce7c

def z717 : W := mkw 0x405776ef5550003f 0xc080aeeddeaaa000 0xe003fffffff8003f 0xc1c007fffffff000

def z718 : W := mkw 0x00141b342a2b7486 0x0c002836685456e9 0x27bc3f7c7f7fc18d 0x8c4f787ef8feff83

def z719 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4003fffc0000c7c1 0xc08007fff800018f

def z720 : W := mkw 0x1602ac00a006a020 0x002c055801400d40 0xfe03ff03e007f85f 0xdffc07fe07c00ff0

def z721 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4473fffc00000001 0xd088e7fff8000000

def z722 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fef80014 0x3f7ff80007fdf000

def z723 : W := mkw 0x1fec43875dd85acb 0xc43fd8870ebbb0b5 0xbd30478fe660ffc5 0x457a608f1fccc1ff

def z724 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd88380ff8707c7ef 0xc9b10701ff0e0f8f

def z725 : W := mkw 0x0000010008005000 0x00000002001000a0 0x02cc478c1998fffb 0x7a05988f183331ff

def z726 : W := mkw 0x7fafa74fdd54d073 0xe0ff5f4e9fbaa9a0 0xda8f870f9918c009 0x09b51f0e1f323180

def z727 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd983c0ff8707ffff 0xffb30781ff0e0fff

def z728 : W := mkw 0x5fff76ec00880afe 0x04bffeedd8011015 0x5ffffffc00980001 0xfebffffff8013000

def z729 : W := mkw 0x1628000355500041 0xc02c500006aaa000 0xa6fc0003fff8003e 0x3b4df80007fff000

def z730 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0xd88380ff8107c7ef 0xefb10701ff020f8f

def z731 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4203fffc00000001 0xda8407fff8000000

def z732 : W := mkw 0x1fab244b55500071 0xc03f564896aaa000 0xfffffffffff8003f 0xfffffffffffff000

def z733 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4003ff7000000000 0x808007fee0000000

def z734 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff83f807fe7f 0xfffc07ff07f00ffc

def z735 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff80034 0x357ff80007fff000

def z736 : W := mkw 0x3652f5b2daa5de2d 0x286ca5eb65b54bbc 0xdb7387f39ee0c629 0x29b6e70fe73dc18c

def z737 : W := mkw 0x165676a40000002e 0x002caced48000000 0x5ffffffc00000001 0xfebffffff8000000

def z738 : W := mkw 0x005058b022ab2e8c 0x0c00a0b16045565d 0x257078f067ff3ff6 0xf64ae0f1e0cffe7f

def z739 : W := mkw 0x20008913ff8fff81 0xb440011227ff1fff 0xa0000003ff9ffffe 0x0140000007ff3fff

def z740 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd9c380ff8787c7ff 0xffb38701ff0f0f8f

def z741 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7e9 0xe9b30701ff0e0f8f

def z742 : W := mkw 0x69fddbeef806f05f 0x20d3fbb7ddf00de0 0xa1fc00fff807f85e 0x2143f801fff00ff0

def z743 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x253078f066673e66 0xe64a60f1e0ccce7c

def z744 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xdbcf80ff8707c7ef 0xffb79f01ff0e0f8f

def z745 : W := mkw 0x405776ec00880abe 0x0480aeedd8011015 0x40cffffc019807a1 0xe0819ffff803300f

def z746 : W := mkw 0x5faf2e5c22a32e72 0x08bf5e5cb845465c 0x7a8f870c66e73e77 0x08f51f0e18cdce7c

def z747 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0xfc03ff03e007f85f 0xdff807fe07c00ff0

def z748 : W := mkw 0x5fff76ee5000007f 0x00bffeeddca00000 0x7ffffffc78000011 0xfefffffff8f00000

def z749 : W := mkw 0x5fff76ec0050007e 0x40bffeedd800a000 0x5ffffffc00f80001 0xfebffffff801f000

def z750 : W := mkw 0x0983244800000030 0x0013064890000000 0x5983fffc00000001 0xeeb307fff8000000

def z751 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5fb3fffc00000001 0xfebf67fff8000000

def z752 : W := mkw 0x4013346800000034 0x00802668d0000000 0x4003ff7000000001 0xc08007fee0000000

def z753 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1998fffa 0x3005988f183331ff

def z754 : W := mkw 0x0010183022232404 0x0800203060444648 0x2530787066673844 0xc44a60f0e0ccce70

def z755 : W := mkw 0x1612342000000024 0x002c246840000000 0x5f33ff7000000001 0xdebe67fee0000000

def z756 : W := mkw 0x1fc766cc0000003a 0x003f8ecd98000000 0x5fcffffc00000001 0xfebf9ffff8000000

def z757 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7ef 0x29b30701ff0e0f8f

def z758 : W := mkw 0x5fff76ee5000007f 0x00bffeeddca00000 0xdfffffff98000009 0xffbfffffff300000

def z759 : W := mkw 0x00545ab422ab2e8e 0x0c00a8b56845565d 0x27fc7ffc67ff3ff7 0xfe4ff8fff8cffe7f

def z760 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4083fffc00000001 0xea8107fff8000000

def z761 : W := mkw 0x362aad02f856f061 0x606c555a05f0ade0 0xfeffff03f9fff87f 0xfffdfffe07f3fff0

def z762 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f859 0xd9fc07fe07f00ff0

def z763 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1998ffe9 0x6805988f183331ff

def z764 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7ad 0xadb30701ff0e0f8f

def z765 : W := mkw 0x0010183022a32e04 0x080020306045465c 0x2570387066e73e76 0xb64ae070e0cdce7c

def z766 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f067e7fffe 0xf64ae0f1e0cfcfff

def z767 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc1800001b 0xfebffffff8300000

def z768 : W := mkw 0x0010183022a32e04 0x080020306045465c 0x2530387066e73814 0x844a6070e0cdce70

def z769 : W := mkw 0x5fbf366f55500077 0xc0bf7e6cdeaaa000 0xffbfbf7fff78000d 0x8dff7f7efffef000

def z770 : W := mkw 0x09d552ec0000001e 0x0013aaa5d8000000 0x5ffffffc00000001 0xfebffffff8000000

def z771 : W := mkw 0x3f808913ff07f501 0xb07f011227fe0fea 0xbf800003ff07fffe 0x3f7f000007fe0fff

def z772 : W := mkw 0x5fff76ee5000007f 0x00bffeeddca00000 0xfffffffff998003f 0xfffffffffff33000

def z773 : W := mkw 0x49d776ed0500003e 0x8093aeedda0a0000 0xd983ffff8700002f 0xefb307ffff0e0000

def z774 : W := mkw 0x5fff76ec00880afe 0x04bffeedd8011015 0x5ffffffc199807bb 0xfebffffff833300f

def z775 : W := mkw 0x09d1d8e9a5a6ab1c 0x9813a3b1d34b4d56 0xfcf3f80fe1e0f999 0x19f9e7f01fc3c1f3

def z776 : W := mkw 0x5fff76ec00880afe 0x04bffeedd8011015 0x5ffffffc00000781 0xfebffffff800000f

def z777 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x424ffffc00000001 0xd0849ffff8000000

def z778 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xda03ff039807f84f 0xcfb407fe07300ff0

def z779 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0xd90380ff8607c7ef 0xefb20701ff0c0f8f

def z780 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfffffffffff8c7ff 0xfffffffffffff18f

def z781 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbf7c0003fff8003e 0x157ef80007fff000

def z782 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x477ffffc00000001 0xf68efffff8000000

def z783 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe83ff0ff907f9df 0xdffd07fe1ff20ff3

def z784 : W := mkw 0x1fa9004b55500051 0xc03f520096aaa000 0xffff8073fff8003e 0xbfffff00e7fff000

def z785 : W := mkw 0x29aaad01ad56f060 0xe053555a035aade0 0x41ffff0007fff861 0xe083fffe000ffff0

def z786 : W := mkw 0x00545ab422a32e0e 0x0800a8b56845465c 0x277c7ff066e73e76 0xf64ef8ffe0cdce7c

def z787 : W := mkw 0x00545ab422a32e0e 0x0800a8b56845465c 0x27fc7ffc67e7ffff 0xfe4ff8fff8cfcfff

def z788 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73e54 0xd44ae0f1e0cdce7c

def z789 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfc03ff03e0073804 0x85f807fe07c00e70

def z790 : W := mkw 0x1faa240355500061 0xc03f544806aaa000 0xffff8703fff8003f 0x3fffff0e07fff000

def z791 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0083fff8067e 0x7f7ff80107fff00c

def z792 : W := mkw 0x20008913ff07f501 0xb040011227fe0fea 0xa0000003fe07f85e 0x0140000007fc0ff0

def z793 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x7ffffffc7ff8003f 0xfefffffff8fff000

def z794 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x028c478c1918ffeb 0x6a05188f183231ff

def z795 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4403fffc00000001 0xd68807fff8000000

def z796 : W := mkw 0x1629805ad2558551 0x502c5300b5a4ab0a 0x667f80fc78ffc7d1 0xd0ccff01f8f1ff8f

def z797 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e7fe7f 0xfe4ae0f1e0cdcffc

def z798 : W := mkw 0x1fa9004b55500051 0xc03f520096aaa000 0xbffc00fffff8003e 0x3f7ff801fffff000

def z799 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f07fff3e7e 0xf64ae0f1e0fffe7c

def z800 : W := mkw 0x20008911af07f500 0xb0400112235e0fea 0x800000038707ffee 0x01000000070e0fff

def z801 : W := mkw 0x0000801082058400 0x0000010021040b08 0xd98380ff8707c7ef 0xefb30701ff0e0f8f

def z802 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x5ffffffc19983e7b 0xfebffffff833307c

def z803 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfecfff8ff99fffff 0xfffd9fff1ff33fff

def z804 : W := mkw 0x0000081022032400 0x0000001020440648 0x257078f066e73e76 0xf64ae0f1e0cdce7c

def z805 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f907ffff 0xdffc07fe07f20fff

def z806 : W := mkw 0x165274a00000002c 0x002ca4e940000000 0x5e03fff000000001 0xdebc07ffe0000000

def z807 : W := mkw 0x5fab244b55500071 0xc0bf564896aaa000 0xffff8003fff8003e 0x3fffff0007fff000

def z808 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfffffffff918001f 0xfffffffffff23000

def z809 : W := mkw 0x0010183022232404 0x0800203060444648 0x2530387066673856 0x844a6070e0ccce70

def z810 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x5803fffc00000001 0xceb007fff8000000

def z811 : W := mkw 0x3f832d5b7f037531 0xb07f065ab6fe06ea 0x27807ffc7f003fb0 0x304f00fff8fe007f

def z812 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xdb8380ff9f07c7ff 0xffb70701ff3e0f8f

def z813 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4173fffc00000001 0xe082e7fff8000000

def z814 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x47fffffc00000001 0xf08ffffff8000000

def z815 : W := mkw 0x49fd52fd07f10e5e 0xc893faa5fa0fe21c 0x01fc00fc07f80620 0x2003f801f80ff00c

def z816 : W := mkw 0x20008913ff57f501 0xf040011227feafea 0xa0000003fffffffe 0x0140000007ffffff

def z817 : W := mkw 0x1fa9004b55500051 0xc03f520096aaa000 0xffff80fffff8c7ff 0xffffff01fffff18f

def z818 : W := mkw 0x49fd52fd07a10f5e 0x9893faa5fa0f421e 0x01fc00fc07e007a0 0x2003f801f80fc00f

def z819 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00000663 0xfebffffff800000c

def z820 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xffffffffff78000d 0xfffffffffffef000

def z821 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x277c78f07eff3e76 0xf64ef8f1e0fdfe7c

def z822 : W := mkw 0x00545ab422a32e0e 0x0800a8b56845465c 0x25fc78fc66e73e76 0xf64bf8f1f8cdce7c

def z823 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xdd83f8ff8707c7ef 0xffbb07f1ff0e0f8f

def z824 : W := mkw 0x1603244800000030 0x002c064890000000 0x5e03fffc00000001 0xdebc07fff8000000

def z825 : W := mkw 0x0004030408085082 0x04000806081010a1 0x028c478c1918fffb 0x7a05188f183231ff

def z826 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5bfffffc00000001 0xe8b7fffff8000000

def z827 : W := mkw 0x5fff76ec000800fe 0x04bffeedd8001001 0x5ffffffc01180181 0xfebffffff8023003

def z828 : W := mkw 0x407f76ec0000007e 0x0080feedd8000000 0x407ffffc00000001 0xc080fffff8000000

def z829 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0xbd7078f3e6e73e7e 0xff7ae0f1e7cdce7c

def z830 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5fbfbffc00000001 0xeebf7f7ff8000000

def z831 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x253078f066673e56 0xd64a60f1e0ccce7c

def z832 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1918ffc9 0x7a05988f183231ff

def z833 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfffffffffef80015 0xfffffffffffdf000

def z834 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xffffffffe760002f 0xffffffffffcec000

def z835 : W := mkw 0x005453a408885a8e 0x0400a8a7481110b5 0x03fc47fc1998fffb 0x7a07f88ff83331ff

def z836 : W := mkw 0x2056ffb4aaaffeae 0x2c40adff69555ffd 0x4003fffc0007ffc1 0xc08007fff8000fff

def z837 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc008ffff807be 0x3f7ff8011ffff00f

def z838 : W := mkw 0x362aad02f856f061 0x606c555a05f0ade0 0xff7fff03fefff87f 0xfffefffe07fdfff0

def z839 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc4003fff8387e 0x7f7ff88007fff070

def z840 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078fc66e7fff7 0xf64ae0f1f8cdcfff

def z841 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xffff8003fff8003f 0xffffff0007fff000

def z842 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd88380ff8107c7eb 0xebb10701ff020f8f

def z843 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5a8fbf7c00000001 0x88b51f7ef8000000

def z844 : W := mkw 0x00545ab422ab2e8e 0x0c00a8b56845565d 0x257078fc66e73ff6 0xf64ae0f1f8cdce7f

def z845 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x2570787066e73836 0xb64ae0f0e0cdce70

def z846 : W := mkw 0x1628000355500041 0xc02c500006aaa000 0xa77c0003fff8003e 0x374ef80007fff000

def z847 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1998ffb9 0x3805988f183331ff

def z848 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f85f 0x19fc07fe07f00ff0

def z849 : W := mkw 0x5fbb356808885af4 0x04bf766ad01110b5 0x5d33b8701998fffa 0x84ba6770e03331ff

def z850 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xddf380ff8707c7ef 0xffbbe701ff0e0f8f

def z851 : W := mkw 0x1ffa74a00000006c 0x003ff4e940000000 0x5ffffff000000001 0xfebfffffe0000000

def z852 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f99ff87f 0xdffc07fe07f33ff0

def z853 : W := mkw 0x1fa9004b55500151 0xd03f520096aaa002 0xbffc000ffff801be 0x3f7ff8001ffff003

def z854 : W := mkw 0x005453a408885a8e 0x0400a8a7481110b5 0x06fc7f8c1998fffb 0x7a0df8ff183331ff

def z855 : W := mkw 0x5fff76ee5050007f 0x40bffeeddca0a000 0xfffffffff8f8001f 0xfffffffffff1f000

def z856 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00800033 0xfebffffff8010000

def z857 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03e007f845 0xdffc07fe07c00ff0

def z858 : W := mkw 0x005453a408a85a8e 0x0c00a8a7481150b5 0x02fc478c19f8fffb 0x7a05f88f1833f1ff

def z859 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfc03ff03e007f857 0xd7f807fe07c00ff0

def z860 : W := mkw 0x09a8000355500041 0xc013500006aaa000 0xa3fc0003fff8003e 0x3b47f80007fff000

def z861 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5fbfff7c00000001 0xdebf7ffef8000000

def z862 : W := mkw 0x3602ac02f006a021 0x206c055805e00d40 0xfe03ff03e0073857 0xdffc07fe07c00e70

def z863 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff80038 0x397ff80007fff000

def z864 : W := mkw 0x3fa88913ff57f541 0xf07f511227feafea 0xbffc0003fffffffe 0x3f7ff80007ffffff

def z865 : W := mkw 0x1f83244b55000031 0x803f064896aa0000 0xff83ffffff00003f 0xffff07fffffe0000

def z866 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xffffff03fffff87f 0xfffffffe07fffff0

def z867 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xfdb380ffe767c7ef 0xeffb6701ffcecf8f

def z868 : W := mkw 0x565776ec0000003e 0x00acaeedd8000000 0x4603fffc00000001 0xd08c07fff8000000

def z869 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7cd 0xcdb30701ff0e0f8f

def z870 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5f33fffc00000001 0xdebe67fff8000000

def z871 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380ff8707c7ef 0xc5b20701ff0e0f8f

def z872 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0xffffffffe7e0003f 0xffffffffffcfc000

def z873 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5d33ff7000000000 0x84ba67fee0000000

def z874 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xdfffffff80000001 0xffbfffffff000000

def z875 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f855 0xd5fc07fe07f00ff0

def z876 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4103fffc00000001 0xe68207fff8000000

def z877 : W := mkw 0x00545ab422a32e0e 0x0800a8b56845465c 0x25707ffc66e73e77 0xf64ae0fff8cdce7c

def z878 : W := mkw 0x00008911afafff80 0x9c000112235f5fff 0xa0000003fffffffe 0x0140000007ffffff

def z879 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x7ffffffc66e03e77 0xfefffffff8cdc07c

def z880 : W := mkw 0x0004030408885a82 0x04000806081110b5 0x028c078c1998fffb 0x6a05180f183331ff

def z881 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xffff80ffffffc7ff 0xffffff01ffffff8f

def z882 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5dfffffc00000001 0xe4bbfffff8000000

def z883 : W := mkw 0x565776ee5000003f 0x00acaeeddca00000 0xfe03fffff800001f 0xdffc07fffff00000

def z884 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe43ff03f887f87f 0xfffc87fe07f10ff0

def z885 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5acffffc00000001 0xfab59ffff8000000

def z886 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5b8ffffc00000001 0xeeb71ffff8000000

def z887 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfd33ffffe6600005 0xc5fa67ffffccc000

def z888 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xdb83c7ff8707c7ef 0xffb7078fff0e0f8f

def z889 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x26cc478c7998ffff 0x7e4d988f18f331ff

def z890 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xf98380ffe7e7c7ff 0xeff30701ffcfcf8f

def z891 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5d33ff7000000001 0xc4ba67fee0000000

def z892 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1998fff1 0x7005988f183331ff

def z893 : W := mkw 0x005453a408885a8e 0x0400a8a7481110b5 0x02cc7ffc1998fffb 0xfa0598fff83331ff

def z894 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00003853 0xfebffffff8000070

def z895 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x5acfc78c1998fffb 0xfeb59f8f183331ff

def z896 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xa7fc0003fff8003e 0x314ff80007fff000

def z897 : W := mkw 0x49d776ec0000003e 0x0093aeedd8000000 0x4183fffc00000001 0xe08307fff8000000

def z898 : W := mkw 0x005058a02002200c 0x0000a0b140400440 0x257078f066e73876 0xf64ae0f1e0cdce70

def z899 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5fffbffc00000001 0xacbfff7ff8000000

def z900 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00000000 0xb4bffffff8000000

def z901 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x4433fffc00000001 0xc08867fff8000000

def z902 : W := mkw 0x5fff76ed0550007e 0xc0bffeedda0aa000 0x7ffffffc67f80037 0xfefffffff8cff000

def z903 : W := mkw 0x0055dbfcaaafff9e 0x1c00abb7f9555fff 0x4003fffc0007ffc1 0xc08007fff8000fff

def z904 : W := mkw 0x767e7fa6788a7aef 0x24ecfcff4cf114f5 0x267c7f0078983810 0x104cf8fe00f13070

def z905 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380ff8607c7cf 0xcfb20701ff0c0f8f

def z906 : W := mkw 0x0010183022a32e04 0x080020306045465c 0x2530787066e73e76 0xd64a60f0e0cdce7c

def z907 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257038f066e73e76 0xa44ae071e0cdce7c

def z908 : W := mkw 0x0004030408885a82 0x04000806081110b5 0x028c070c1918ffc9 0x0805180e183231ff

def z909 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff8001c 0x1d7ff80007fff000

def z910 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x6573fffc66e00037 0xf6cae7fff8cdc000

def z911 : W := mkw 0x49ff76ec0000007e 0x0093feedd8000000 0x408ffffc00000001 0xc0811ffff8000000

def z912 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xffffff73fff8003e 0xbffffffee7fff000

def z913 : W := mkw 0x20008912faa7fe01 0x2840011225f54ffc 0xa0000003f807fe5e 0x0140000007f00ffc

def z914 : W := mkw 0x5fff76ef5500007f 0x80bffeeddeaa0000 0xffffffffff00003f 0xfffffffffffe0000

def z915 : W := mkw 0x5fff76ed0550007e 0xc0bffeedda0aa000 0xdfffffff87f8002f 0xffbfffffff0ff000

def z916 : W := mkw 0x0001805987058510 0x90000300b30e0b0a 0xd80380ff8707c7ef 0xcfb00701ff0e0f8f

def z917 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc1998c7fb 0xfebffffff833318f

def z918 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5f33ff7000000000 0x94be67fee0000000

def z919 : W := mkw 0x1f83244800000030 0x003f064890000000 0x5f03ff7000000001 0xdebe07fee0000000

def z920 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc0000c7c1 0xfebffffff800018f

def z921 : W := mkw 0x1628000355500041 0xc02c500006aaa000 0xa67c0003fef80014 0x114cf80007fdf000

def z922 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8607c7c5 0xefb30701ff0c0f8f

def z923 : W := mkw 0x5fff76ee5050007f 0x40bffeeddca0a000 0x5ffffffc18180001 0xfebffffff8303000

def z924 : W := mkw 0x1fa9004b55500051 0xc03f520096aaa000 0xffff800ffff8003f 0x3fffff001ffff000

def z925 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0xd80380ff8007c7c9 0xc9b00701ff000f8f

def z926 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5fffff7000000000 0xbebffffee0000000

def z927 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbbfc0003fff8003e 0x2977f80007fff000

def z928 : W := mkw 0x09a9805987558550 0xd0135300b30eab0a 0xfdff80ffe7ffc7ff 0xfffbff01ffcfff8f

def z929 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xda03ff039807f85b 0xdbb407fe07300ff0

def z930 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5fffff7c00000001 0x9cbffffef8000000

def z931 : W := mkw 0x5fbb346b55500075 0xc0bf7668d6aaa000 0xffffff73fff8003f 0xfffffffee7fff000

def z932 : W := mkw 0x565776ec0000003e 0x00acaeedd8000000 0x5c03fffc00000001 0xc4b807fff8000000

def z933 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc078c1998fffb 0x2805980f183331ff

def z934 : W := mkw 0x005274a00000002c 0x0000a4e940000000 0x4003fff000000001 0xc08007ffe0000000

def z935 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73e76 0x304ae0f1e0cdce7c

def z936 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0xda03ff039807f85f 0xdfb407fe07300ff0

def z937 : W := mkw 0x405776ec00880abe 0x0480aeedd8011015 0x4003fffc00000781 0xc08007fff800000f

def z938 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x27fc78fc7fffffff 0xfe4ff8f1f8ffffff

def z939 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc0100c189 0xfebffffff8020183

def z940 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc06000027 0xfebffffff80c0000

def z941 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0x5ffffffc07000021 0xfebffffff80e0000

def z942 : W := mkw 0x0981805882058510 0x10130300b1040b0a 0xd98380ff8007c7cf 0xefb30701ff000f8f

def z943 : W := mkw 0x00545ab422ab2e8e 0x0c00a8b56845565d 0x27fc78fc7fff3ffe 0xfe4ff8f1f8fffe7f

def z944 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe83ff03f907f87f 0xfffd07fe07f20ff0

def z945 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5fffff7000000001 0xfebffffee0000000

def z946 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x07fc478c1998fffb 0x7e0ff88f183331ff

def z947 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd80380ff8007c7c1 0xc1b00701ff000f8f

def z948 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5803fffc00000001 0xc0b007fff8000000

def z949 : W := mkw 0x0004030408885a82 0x04000806081110b5 0x02cc070c1998fffb 0x3a05980e183331ff

def z950 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f81d 0x9dfc07fe07f00ff0

def z951 : W := mkw 0x4017366c00000036 0x00802e6cd8000000 0x4003bf7c00000001 0x8080077ef8000000

def z952 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f8073815 0xdffc07fe07f00e70

def z953 : W := mkw 0x005058b02223240c 0x0800a0b160444648 0x257078f066673856 0xf64ae0f1e0ccce70

def z954 : W := mkw 0x20008910aa07f500 0x3040011221540fea 0x000000000007ffc0 0x0000000000000fff

def z955 : W := mkw 0x567e76a40000006e 0x00acfced48000000 0x5f7ffff000000001 0xfebeffffe0000000

def z956 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd88380ff8107c7cf 0xcfb10701ff020f8f

def z957 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc4703fff8003f 0x7f7ff88e07fff000

def z958 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x428ffffc00000001 0xc8851ffff8000000

def z959 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc0100002b 0xfebffffff8020000

def z960 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc18980011 0xfebffffff8313000

def z961 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x46fffffc00000001 0xfa8dfffff8000000

def z962 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x03cc478c1f98ffff 0x7e07988f183f31ff

def z963 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x7d73f8f066e73e77 0xfefae7f1e0cdce7c

def z964 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x253078f066e73e76 0xc44a60f1e0cdce7c

def z965 : W := mkw 0x36008912faa7fe01 0x286c011225f54ffc 0xbf700003fee7fe7e 0x3f7ee00007fdcffc

def z966 : W := mkw 0x405776ec00800a3e 0x0080aeedd8010014 0x4003fffc00003e41 0xc08007fff800007c

def z967 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0xd803ff038007f849 0xc9b007fe07000ff0

def z968 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x26fc478c79f8fffb 0x7a4df88f18f3f1ff

def z969 : W := mkw 0x0028000355500041 0xc000500006aaa000 0xa07c0003fff8003e 0x0140f80007fff000

def z970 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc008ffff8003f 0x7f7ff8011ffff000

def z971 : W := mkw 0x1faa240355500061 0xc03f544806aaa000 0xffffb803fff8003e 0xbfffff7007fff000

def z972 : W := mkw 0x3602ad02f80ef0a1 0x246c055a05f01de1 0xfe03ff03f91ff9df 0xdffc07fe07f23ff3

def z973 : W := mkw 0x5faf264c00000072 0x00bf5e4c98000000 0x5f8ffffc00000001 0xfebf1ffff8000000

def z974 : W := mkw 0x0981804880048010 0x0013030091000900 0xd98380ff8107c7ef 0xefb30701ff020f8f

def z975 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff8c7fe 0x3f7ff80007fff18f

def z976 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe73ff03f8e7f85f 0xdffce7fe07f1cff0

def z977 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x22cc478c7ff8ffff 0x7a45988f18fff1ff

def z978 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5f3fbf7000000000 0x84be7f7ee0000000

def z979 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc06e00021 0xfebffffff80dc000

def z980 : W := mkw 0x3faba54bdd54d171 0xf07f574a97baa9a2 0xda8f870f9918c189 0x09b51f0e1f323183

def z981 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xff7fff73fef80014 0x95fefffee7fdf000

def z982 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xfffffffffe60001f 0xfffffffffffcc000

def z983 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfa03ff03f807f85f 0xc9f407fe07f00ff0

def z984 : W := mkw 0x165274a25000002d 0x002ca4e944a00000 0xff73fff3fee0003f 0xfffee7ffe7fdc000

def z985 : W := mkw 0x3fabac5bf757a571 0xf07f5758b7eeaf4a 0xfd33b873e6670004 0x85fa6770e7ccce00

def z986 : W := mkw 0x1600000250000001 0x002c000004a00000 0xbffc0003fff8003e 0x3f7ff80007fff000

def z987 : W := mkw 0x09a9805987058550 0x90135300b30e0b0a 0xd9ff80ff8707c7ef 0xefb3ff01ff0e0f8f

def z988 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xdfffffff9998003b 0xffbfffffff333000

def z989 : W := mkw 0x565776ec0000003e 0x00acaeedd8000000 0x5ecffffc00000001 0xfebd9ffff8000000

def z990 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4043fffc00000001 0xf28087fff8000000

def z991 : W := mkw 0x09a8000355500041 0xc013500006aaa000 0xa5fc0003fff8003e 0x374bf80007fff000

def z992 : W := mkw 0x20008913ffa7ff01 0xb840011227ff4ffe 0xa0000003ffe7fffe 0x0140000007ffcfff

def z993 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03fee7f87f 0xdffc07fe07fdcff0

def z994 : W := mkw 0x565776ec0000003e 0x00acaeedd8000000 0x5a03fffc00000001 0xc8b407fff8000000

def z995 : W := mkw 0x2002ad02f806f021 0x2040055a05f00de0 0xf803ff03f807f85f 0xcff007fe07f00ff0

def z996 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xff73ff03f807f85f 0xfffee7fe07f00ff0

def z997 : W := mkw 0x0980000105000000 0x80130000020a0000 0xbffc0003fff8003e 0x3f7ff80007fff000

def z998 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807381e 0x9ffc07fe07f00e70

def z999 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff8c07f 0x7f7ff80007fff180

def z1000 : W := mkw 0x49d776ec0000003e 0x0093aeedd8000000 0x5903fffc00000001 0xc4b207fff8000000

def z1001 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x27707ff066e73e77 0xfe4ee0ffe0cdce7c

def z1002 : W := mkw 0x5fbf366f55500077 0xc0bf7e6cdeaaa000 0xffffbf7ffff8003f 0xbfffff7efffff000

def z1003 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7e5 0xe5b30701ff0e0f8f

def z1004 : W := mkw 0x20008913fff7fe01 0xe840011227ffeffc 0xa0000003fffffe7e 0x0140000007fffffc

def z1005 : W := mkw 0x20008912fa27f401 0x2840011225f44fe8 0xa0000003fe67f85e 0x0140000007fccff0

def z1006 : W := mkw 0x3602ad00a806f020 0x206c055a01500de0 0xde03ff038007f84f 0xdfbc07fe07000ff0

def z1007 : W := mkw 0x0000000355500001 0xc000000006aaa000 0xa7fc0003fff8003e 0x3f4ff80007fff000

def z1008 : W := mkw 0x49d776ec0000003e 0x0093aeedd8000000 0x5df3fffc00000001 0xfebbe7fff8000000

def z1009 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd9cf80ff879fc7ef 0xefb39f01ff0f3f8f

def z1010 : W := mkw 0x5fff76ed0550007e 0xc0bffeedda0aa000 0x5ffffffc1ff8003b 0xfebffffff83ff000

def z1011 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xff03ff03fe07f87f 0xfffe07fe07fc0ff0

def z1012 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x7ffffffc60000017 0xfefffffff8c00000

def z1013 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x028c478c1918ffdb 0x5a05188f183231ff

def z1014 : W := mkw 0x5fff76ed0550007e 0xc0bffeedda0aa000 0x5ffffffc06600001 0xfebffffff80cc000

def z1015 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8707c7ee 0xa5b30701ff0e0f8f

def z1016 : W := mkw 0x5fff76ef55d00a7f 0xc0bffeeddeaba014 0xfffffffffff83e7f 0xfffffffffffff07c

def z1017 : W := mkw 0x5fff76ee5050007f 0x40bffeeddca0a000 0x7ffffffc60600001 0xfefffffff8c0c000

def z1018 : W := mkw 0x362aad02f856f061 0x606c555a05f0ade0 0xfe33ff03f867f85f 0xdffc67fe07f0cff0

def z1019 : W := mkw 0x5fff76ed05d80afe 0xc4bffeedda0bb015 0x5ffffffc07f807a1 0xfebffffff80ff00f

def z1020 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xffffffffe7f80025 0xffffffffffcff000

def z1021 : W := mkw 0x5fff76ec00a00a7e 0x08bffeedd8014014 0x5ffffffc00e00001 0xfebffffff801c000

def z1022 : W := mkw 0x1628000250500041 0x402c500004a0a000 0xbf7c0003fef8003e 0x3f7ef80007fdf000

def z1023 : W := mkw 0x1ff858b377f32e4d 0xc83ff0b166efe65c 0x9a8c78f3991f3e48 0xc93518f1e7323e7c

def z1024 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0xdfffffff81000009 0xffbfffffff020000

def z1025 : W := mkw 0x5fff76ec00880afe 0x04bffeedd8011015 0x5ffffffc01983ff3 0xfebffffff803307f

def z1026 : W := mkw 0x09a8000355500041 0xc013500006aaa000 0xb9fc0003fff8003e 0x2f73f80007fff000

def z1027 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5f7ffff000000000 0xf6beffffe0000000

def z1028 : W := mkw 0x00545ab422ab2e8e 0x0c00a8b56845565d 0x257c78f066ff3e76 0xf64af8f1e0cdfe7c

def z1029 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xde03ff039807f849 0xdfbc07fe07300ff0

def z1030 : W := mkw 0x00545ab422ab2e8e 0x0c00a8b56845565d 0x25fc78fc67ffffff 0xfe4bf8f1f8cfffff

def z1031 : W := mkw 0x09d552fd07a90f9e 0x9c13aaa5fa0f521f 0x01fc00fc07f807a0 0x2003f801f80ff00f

def z1032 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00070047 0xfebffffff8000e00

def z1033 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x25f078fc66e73e77 0xfe4be0f1f8cdce7c

def z1034 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5f7ffffc00000001 0xd4befffff8000000

def z1035 : W := mkw 0x0003244800000030 0x0000064890000000 0x4003fffc00000001 0xc08007fff8000000

def z1036 : W := mkw 0x005453a408885a8e 0x0400a8a7481110b5 0x27fc7ffc7ff8ffff 0xfe4ff8fff8fff1ff

def z1037 : W := mkw 0x49fd52fd07890fde 0x9493faa5fa0f121f 0x01fc00fc079807a0 0x2003f801f80f300f

def z1038 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x2570787066e73856 0xd64ae0f0e0cdce70

def z1039 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xda8fffff99180009 0xc9b51fffff323000

def z1040 : W := mkw 0x5fbb346800000074 0x00bf7668d0000000 0x5f33bf7000000001 0x8cbe677ee0000000

def z1041 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x03fc478c1ff8fffb 0x7a07f88f183ff1ff

def z1042 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f8073856 0xd7fc07fe07f00e70

def z1043 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd90380ff8607c7e7 0xe7b20701ff0c0f8f

def z1044 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f85e 0x95fc07fe07f00ff0

def z1045 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x06cc7f8c1998fffb 0xfe0d98ff183331ff

def z1046 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066673e44 0xf64ae0f1e0ccce7c

def z1047 : W := mkw 0x005274a00000002c 0x0000a4e940000000 0x4573fff000000001 0xf68ae7ffe0000000

def z1048 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x2530787066673804 0x844a60f0e0ccce70

def z1049 : W := mkw 0x20008912fa07f401 0x2040011225f40fe8 0xa0000003fe07fe7e 0x0140000007fc0ffc

def z1050 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff8ff807ffdf 0xdffc07ff1ff00fff

def z1051 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5f7fff7000000001 0xdebefffee0000000

def z1052 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x7ffffffc60e00011 0xfefffffff8c1c000

def z1053 : W := mkw 0x49d776ec0000003e 0x0093aeedd8000000 0x5bcffffc00000001 0xfeb79ffff8000000

def z1054 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x277078f07ee73e7e 0xfe4ee0f1e0fdce7c

def z1055 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003ffff007e 0xff7ff80007fffe00

def z1056 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73814 0xf64ae0f1e0cdce70

def z1057 : W := mkw 0x1fd374e80000003c 0x003fa6e9d0000000 0x5ff3fffc00000001 0xfebfe7fff8000000

def z1058 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x5ffffffc00803811 0xfebffffff8010070

def z1059 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x42cffffc1998003b 0xfa859ffff8333000

def z1060 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xd803ff038007f841 0xc1b007fe07000ff0

def z1061 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfc03ff03e007f84f 0xcff807fe07c00ff0

def z1062 : W := mkw 0x1602240000000020 0x002c044800000000 0x5f03fff000000001 0xfebe07ffe0000000

def z1063 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xdb8f80ff9f1fc7ef 0xefb71f01ff3e3f8f

def z1064 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbdfc0003fff8003e 0x257bf80007fff000

def z1065 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc19180009 0xfebffffff8323000

def z1066 : W := mkw 0x49ff76ed0550007e 0xc093feedda0aa000 0x41fffffc07f80021 0xe083fffff80ff000

def z1067 : W := mkw 0x2002ad00a806f020 0x2040055a01500de0 0xd803ff038007f845 0xc5b007fe07000ff0

def z1068 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x028c478c1998fffb 0x4805188f183331ff

def z1069 : W := mkw 0x362aad02f806f061 0x206c555a05f00de0 0xfe7fff03f807f85f 0xdffcfffe07f00ff0

def z1070 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbf7c0003fef80036 0x377ef80007fdf000

def z1071 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe4fff03f89ff85f 0xdffc9ffe07f13ff0

def z1072 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x420ffffc00000001 0xc0841ffff8000000

def z1073 : W := mkw 0x16022c0270022021 0x002c045804e00440 0xfe03ff03f807385f 0xdffc07fe07f00e70

def z1074 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0xdfffffff8700c7ef 0xffbfffffff0e018f

def z1075 : W := mkw 0x5ffb74e80000007c 0x00bff6e9d0000000 0x5f73fff000000001 0xfebee7ffe0000000

def z1076 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4533fffc00000001 0xc48a67fff8000000

def z1077 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xdfffffff9f18002f 0xffbfffffff3e3000

def z1078 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xfd8380ffe707c7ff 0xfffb0701ffce0f8f

def z1079 : W := mkw 0x5fff76ee5000007f 0x00bffeeddca00000 0xfffffffffee0003f 0xfffffffffffdc000

def z1080 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xff03fff3f807f85f 0xfffe07ffe7f00ff0

def z1081 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5d33bf7c00000001 0x84ba677ef8000000

def z1082 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe03ff03f807f84d 0xcdfc07fe07f00ff0

def z1083 : W := mkw 0x20008912faaffe81 0x2c40011225f55ffd 0xa0000003fffffffe 0x0140000007ffffff

def z1084 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfc03ff03f807f85f 0xc5f807fe07f00ff0

def z1085 : W := mkw 0x1fab244800000070 0x003f564890000000 0x5ffffffc00000001 0xfebffffff8000000

def z1086 : W := mkw 0x49ff76ec0000007e 0x0093feedd8000000 0x45fffffc00000001 0xf68bfffff8000000

def z1087 : W := mkw 0x0004030408885a82 0x04000806081110b5 0x028c470c1998fffb 0x5a05188e183331ff

def z1088 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x25f078f067e73e7e 0xfe4be0f1e0cfce7c

def z1089 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5efffffc00000001 0xd8bdfffff8000000

def z1090 : W := mkw 0x1628000355500041 0xc02c500006aaa000 0xbe7c0003fff8003e 0x1f7cf80007fff000

def z1091 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5fbffffc00000001 0xccbf7ffff8000000

def z1092 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c199fffff 0xfe05988f18333fff

def z1093 : W := mkw 0x49ff76ec0000007e 0x0093feedd8000000 0x4133fffc00000001 0xc08267fff8000000

def z1094 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x40cffffc00000001 0xe0819ffff8000000

def z1095 : W := mkw 0x567f76ee5050007f 0x40acfeeddca0a000 0x667ffffc78f80011 0xd0ccfffff8f1f000

def z1096 : W := mkw 0x1faa240355500061 0xc03f544806aaa000 0xbffc7f03fff8003e 0x3f7ff8fe07fff000

def z1097 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff8107c7c9 0xefb30701ff020f8f

def z1098 : W := mkw 0x49ff76ec0000007e 0x0093feedd8000000 0x59fffffc00000001 0xeeb3fffff8000000

def z1099 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x9acc478f9998ffff 0x7f35988f1f3331ff

def z1100 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc478c1998ffd9 0x5805988f183331ff

def z1101 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x27fc78f066e73e76 0xfe4ff8f1e0cdce7c

def z1102 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x5ffffffc00800621 0xfebffffff801000c

def z1103 : W := mkw 0x0010183022232404 0x0800203060444648 0x253078f066673e76 0xf64a60f1e0ccce7c

def z1104 : W := mkw 0x362aad02f856f061 0x606c555a05f0ade0 0xfe0fff03f81ff85f 0xdffc1ffe07f03ff0

def z1105 : W := mkw 0x20008910aaa7fe00 0x2840011221554ffc 0x2000000066e7fe76 0x0040000000cdcffc

def z1106 : W := mkw 0x09a9805987558550 0xd0135300b30eab0a 0xd9b380ff8767c7ef 0xefb36701ff0ecf8f

def z1107 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x03cc47fc1998fffb 0xfe07988ff83331ff

def z1108 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc0003fff8002c 0x2d7ff80007fff000

def z1109 : W := mkw 0x1602a5008804d020 0x002c054a011009a0 0xde03ff039807f85f 0xdfbc07fe07300ff0

def z1110 : W := mkw 0x5fff76ef55d80aff 0xc4bffeeddeabb015 0xfffffffffff807bf 0xfffffffffffff00f

def z1111 : W := mkw 0x00008900a806f000 0x0000011201500de0 0xfe03ff03f807f85f 0xdffc07fe07f00ff0

def z1112 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xff33ff03fe67f85f 0xdffe67fe07fccff0

def z1113 : W := mkw 0x5fff76ee5050007f 0x40bffeeddca0a000 0x7ffffffc7ef80037 0xfefffffff8fdf000

def z1114 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0x7ffffffc7ff80031 0xfefffffff8fff000

def z1115 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbf7c0003fef8001e 0x1f7ef80007fdf000

def z1116 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x467fff7000000000 0x908cfffee0000000

def z1117 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0xdfffffff9f98003f 0xffbfffffff3f3000

def z1118 : W := mkw 0x5fbb346b55500075 0xc0bf7668d6aaa000 0xff33ff73fe60001f 0xdffe67fee7fcc000

def z1119 : W := mkw 0x09a9805987558550 0xd0135300b30eab0a 0xd98f80ff871fc7ef 0xefb31f01ff0e3f8f

def z1120 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5d73fffc00000001 0xf6bae7fff8000000

def z1121 : W := mkw 0x5fff76ed0500007e 0x80bffeedda0a0000 0xdfffffff86000005 0xffbfffffff0c0000

def z1122 : W := mkw 0x5613346800000034 0x00ac2668d0000000 0x5e03ff7000000001 0xdebc07fee0000000

def z1123 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd9f380ff87e7c7ef 0xefb3e701ff0fcf8f

def z1124 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xdfffffff9ff80029 0xffbfffffff3ff000

def z1125 : W := mkw 0x5fff76ee5000007f 0x00bffeeddca00000 0xffffffffe0000005 0xffffffffffc00000

def z1126 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x25f078fc67e73ff6 0xf64be0f1f8cfce7f

def z1127 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x4083fffc0100c7eb 0xea8107fff802018f

def z1128 : W := mkw 0x09a9805987558550 0xd0135300b30eab0a 0xdbff80ff9fffc7ff 0xffb7ff01ff3fff8f

def z1129 : W := mkw 0x0010183022232404 0x0800203060444648 0x2570787066e73876 0xf64ae0f0e0cdce70

def z1130 : W := mkw 0x0981805987558510 0xd0130300b30eab0a 0xd98380ff87ffc7ef 0xefb30701ff0fff8f

def z1131 : W := mkw 0x5fff76ee5050007f 0x40bffeeddca0a000 0x7ffffffc79f8003b 0xfefffffff8f3f000

def z1132 : W := mkw 0x3fa88913fff7fe41 0xe87f511227ffeffc 0xbffc0003fffffe7e 0x3f7ff80007fffffc

def z1133 : W := mkw 0x405776ec0000003e 0x0080aeedd8000000 0x47fffffc00000001 0xfe8ffffff8000000

def z1134 : W := mkw 0x5fbf366c00000076 0x00bf7e6cd8000000 0x5fffbf7c00000001 0xbebfff7ef8000000

def z1135 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfe8fff03f91ff85f 0xdffd1ffe07f23ff0

def z1136 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x5ffffffc0180fffb 0xfebffffff80301ff

def z1137 : W := mkw 0x5fd776ec0000003e 0x00bfaeedd8000000 0x5f83fffc00000001 0xfebf07fff8000000

def z1138 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc7803fff8003e 0xff7ff8f007fff000

def z1139 : W := mkw 0x20008910aaa7fe00 0x2840011221554ffc 0x000000000007fe40 0x0000000000000ffc

def z1140 : W := mkw 0x3602ad02f856f021 0x606c055a05f0ade0 0xfe03ff03f8fff85f 0xdffc07fe07f1fff0

def z1141 : W := mkw 0x0044438408885a8a 0x04008887081110b5 0x02cc470c1998fffb 0x1805988e183331ff

def z1142 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0xdfffffff8000000f 0xffbfffffff000000

def z1143 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x7ffffffc66600005 0xfefffffff8ccc000

def z1144 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbefc0003fff8003e 0x197df80007fff000

def z1145 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc01980021 0xfebffffff8033000

def z1146 : W := mkw 0x00545ab422a32e0e 0x0800a8b56845465c 0x27fc7ffc7fff3e7f 0xfe4ff8fff8fffe7c

def z1147 : W := mkw 0x5fff76ec00800a7e 0x00bffeedd8010014 0x5ffffffc00003e41 0xfebffffff800007c

def z1148 : W := mkw 0x49ff76ec0000007e 0x0093feedd8000000 0x43fffffc00000001 0xfa87fffff8000000

def z1149 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73e70 0xf04ae0f1e0cdce7c

def z1150 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5e8ffffc00000001 0xdebd1ffff8000000

def z1151 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc0000c04b 0xfebffffff8000180

def z1152 : W := mkw 0x0001805882058510 0x10000300b1040b0a 0xd80380ff8007c7c5 0xc5b00701ff000f8f

def z1153 : W := mkw 0x5fff76ec00880afe 0x04bffeedd8011015 0x5ffffffc0198c7eb 0xfebffffff803318f

def z1154 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc000ffff8c1bf 0x3f7ff8001ffff183

def z1155 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x2570787066e73e76 0x944ae0f0e0cdce7c

def z1156 : W := mkw 0x5fff76ed0500017e 0x90bffeedda0a0002 0x5ffffffc01000181 0xfebffffff8020003

def z1157 : W := mkw 0x0010183022a32e04 0x080020306045465c 0x253038f066e73e76 0xe64a6071e0cdce7c

def z1158 : W := mkw 0x3602ad02f806f021 0x206c055a05f00de0 0xfecfff03f807f85f 0xfffd9ffe07f00ff0

def z1159 : W := mkw 0x565776ec0000003e 0x00acaeedd8000000 0x5f73fffc00000001 0xfebee7fff8000000

def z1160 : W := mkw 0x1ffa74a35550006d 0xc03ff4e946aaa000 0xfffffff3fff8003f 0xffffffffe7fff000

def z1161 : W := mkw 0x36567fa678aa7aaf 0x2c6cacff4cf154f5 0x267c7f0078f83810 0x104cf8fe00f1f070

def z1162 : W := mkw 0x49d776ec0000003e 0x0093aeedd8000000 0x5883fffc00000001 0xc8b107fff8000000

def z1163 : W := mkw 0x5fff76ed0550007e 0xc0bffeedda0aa000 0x5ffffffc01180001 0xfebffffff8023000

def z1164 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5db3fffc00000001 0xeebb67fff8000000

def z1165 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73e64 0xe44ae0f1e0cdce7c

def z1166 : W := mkw 0x1fa8000355500041 0xc03f500006aaa000 0xbffc00f3fff8003e 0xff7ff801e7fff000

def z1167 : W := mkw 0x005058b022a32e0c 0x0800a0b16045465c 0x257078f066e73e34 0xb44ae0f1e0cdce7c

def z1168 : W := mkw 0x5fff76ec0000007e 0x00bffeedd8000000 0x5ffffffc00000001 0x38bffffff8000000

def z1169 : W := mkw 0x0010183022232404 0x0800203060444648 0x2530787066673814 0x944a60f0e0ccce70

def z1170 : W := mkw 0x567f76ec0000007e 0x00acfeedd8000000 0x5e7ffffc00000001 0xdebcfffff8000000

def z1171 : W := mkw 0x5fff76ef5550007f 0xc0bffeeddeaaa000 0xffffffffe6e00037 0xffffffffffcdc000

def z1172 : W := mkw 0x0981805987058510 0x90130300b30e0b0a 0xd98380ff9f9fc7ff 0xefb30701ff3f3f8f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z8])],[(0,[z9,z0,z1,z10,z4,z5,z6]),(0,[z0,z1,z2,z11,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z13,z4,z5,z6]),(0,[z9,z0,z1,z14,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z5,z8]),(0,[z16,z0,z1,z17,z4,z5,z6]),(0,[z18,z0,z1,z2,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z20,z5,z8])],[(0,[z0,z1,z21,z2,z4,z5,z6]),(0,[z0,z22,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z4,z5,z24])],[(0,[z0,z1,z2,z4,z25,z5,z6]),(0,[z0,z1,z26,z2,z4,z5,z24])],[(0,[z27,z0,z1,z2,z4,z28,z6]),(0,[z29,z1,z2,z4,z5,z30,z6]),(0,[z0,z1,z2,z10,z4,z5,z24]),(0,[z0,z1,z2,z31,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z6]),(1,[z0,z1,z2,z33,z4,z5])],[(1,[z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z14,z4,z5,z24]),(0,[z35,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z36,z5,z6]),(0,[z0,z1,z2,z37,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z6])],[(0,[z0,z1,z2,z39,z4,z5,z6]),(0,[z40,z1,z2,z4,z5,z6,z41]),(0,[z42,z43,z0,z2,z4,z5,z6]),(0,[z44,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z5,z8])]],
   [[(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z48,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z49,z6])],[(0,[z0,z1,z2,z4,z50,z5,z6]),(0,[z29,z0,z1,z2,z4,z5,z8]),(0,[z0,z51,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z52,z5,z53]),(0,[z0,z1,z2,z4,z5,z54,z6]),(0,[z0,z1,z2,z4,z20,z5,z6]),(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z56,z5,z24]),(0,[z0,z1,z2,z4,z57,z5,z6])],[(0,[z0,z1,z2,z58,z4,z5,z6]),(0,[z0,z1,z2,z59,z4,z5,z6]),(0,[z0,z60,z1,z2,z4,z5,z6])],[(0,[z40,z1,z2,z4,z61,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z24]),(0,[z64,z0,z1,z2,z4,z5,z6])],[(0,[z65,z0,z1,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z66,z6]),(0,[z0,z1,z2,z4,z5,z30,z67]),(0,[z0,z1,z2,z4,z5,z6,z68]),(0,[z69,z70,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z33,z4,z5,z6]),(0,[z0,z1,z2,z71,z4,z5,z24])],[(0,[z29,z40,z1,z2,z4,z5,z6]),(0,[z72,z1,z2,z4,z5,z6,z41]),(0,[z0,z1,z2,z73,z4,z5,z6]),(0,[z74,z0,z2,z4,z5,z53,z6]),(1,[z0,z1,z2,z4,z5,z75]),(0,[z0,z1,z2,z4,z5,z24,z24]),(0,[z0,z1,z2,z4,z5,z6,z76])],[(0,[z0,z1,z2,z4,z77,z5,z6]),(0,[z0,z1,z2,z4,z78,z5,z6]),(0,[z72,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z79,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z5,z6])],[(0,[z80,z0,z1,z2,z4,z5,z8]),(0,[z74,z43,z0,z2,z4,z5,z6]),(0,[z43,z0,z1,z2,z4,z5,z24]),(0,[z81,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z82]),(0,[z0,z1,z2,z83,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z84]),(0,[z0,z1,z2,z4,z5,z85,z6])],[(0,[z0,z1,z2,z4,z5,z8,z41]),(1,[z86,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z87,z4,z5,z6]),(0,[z0,z1,z88,z2,z4,z56,z5])],[(0,[z0,z89,z2,z4,z5,z6,z90]),(0,[z0,z1,z2,z91,z4,z5,z6]),(0,[z27,z1,z2,z4,z5,z92,z6]),(0,[z93,z0,z1,z2,z4,z92,z6]),(0,[z0,z70,z1,z2,z4,z5,z24])],[(0,[z0,z1,z2,z94,z4,z5,z6]),(0,[z0,z1,z95,z2,z45,z5,z6])],[(0,[z96,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z97,z5,z6]),(1,[z0,z98,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z99,z6]),(0,[z0,z1,z2,z100,z4,z5,z6]),(0,[z0,z1,z2,z101,z4,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z24]),(0,[z0,z1,z103,z2,z4,z5,z6])],[(0,[z0,z104,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z105]),(0,[z0,z1,z2,z4,z5,z106,z6]),(0,[z7,z0,z1,z2,z4,z20,z6]),(0,[z107,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z108])],[(0,[z80,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z52,z5]),(0,[z0,z1,z2,z4,z5,z6,z67])],[(1,[z0,z1,z109,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z5,z8]),(0,[z0,z1,z2,z4,z110,z5,z6])]],
   [[(0,[z0,z1,z2,z111,z4,z5,z6]),(0,[z7,z0,z1,z4,z5,z112,z6]),(0,[z0,z1,z26,z2,z4,z113,z6])],[(0,[z114,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z115,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z116]),(0,[z0,z1,z117,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z4,z5,z24])],[(0,[z40,z80,z1,z2,z4,z5,z6]),(0,[z118,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z113,z8])],[(0,[z0,z1,z2,z4,z5,z6,z119]),(0,[z120,z0,z1,z2,z4,z5,z6]),(1,[z42,z0,z2,z4,z5,z121]),(0,[z0,z1,z2,z122,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z123]),(0,[z0,z1,z2,z4,z124,z5,z6]),(1,[z63,z0,z1,z4,z5,z125])],[(0,[z126,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z1,z127,z4,z5,z6]),(0,[z0,z1,z95,z2,z4,z5,z128]),(0,[z0,z1,z95,z2,z4,z5,z24]),(1,[z0,z1,z2,z83,z5,z6])],[(1,[z0,z129,z2,z4,z5,z6]),(0,[z0,z1,z2,z130,z4,z5,z6]),(0,[z0,z1,z4,z45,z131,z5,z6]),(0,[z9,z0,z1,z2,z132,z5,z6]),(0,[z0,z133,z1,z2,z4,z5,z6])]],
   [[(0,[z134,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z135,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z136,z6]),(0,[z0,z1,z2,z4,z137,z5,z24]),(0,[z0,z1,z2,z4,z5,z138,z6]),(0,[z0,z1,z26,z2,z4,z5,z8]),(0,[z0,z1,z2,z71,z4,z113,z6])],[(0,[z0,z139,z1,z2,z4,z5,z6]),(1,[z140,z1,z2,z4,z5,z6]),(0,[z141,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z132,z4,z45,z5,z6]),(1,[z0,z1,z2,z45,z5,z8]),(0,[z0,z142,z1,z2,z4,z5,z6]),(0,[z143,z0,z1,z2,z4,z5,z6])],[(0,[z144,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z145,z5,z8])],[(0,[z0,z1,z146,z2,z4,z5,z6]),(0,[z147,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z148,z4,z5,z6]),(0,[z0,z1,z2,z149,z4,z5,z6]),(1,[z0,z1,z2,z57,z5,z6]),(0,[z0,z1,z2,z135,z4,z6,z150])],[(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z33,z4,z5,z112]),(0,[z0,z1,z2,z4,z5,z152,z6])],[(0,[z80,z0,z89,z2,z4,z5,z6]),(0,[z29,z1,z89,z2,z4,z5,z6]),(0,[z43,z0,z2,z4,z5,z6,z90]),(1,[z0,z1,z2,z4,z153,z6]),(0,[z0,z1,z2,z4,z5,z154,z6]),(1,[z0,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z132,z4,z5,z156]),(0,[z0,z1,z2,z157,z4,z5,z6])],[(1,[z114,z1,z14,z4,z5,z6]),(1,[z74,z0,z2,z4,z53,z6]),(0,[z0,z1,z2,z158,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z159,z6])],[(0,[z134,z0,z1,z2,z4,z5,z6]),(0,[z160,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z71,z5,z8])]],
   [[(0,[z0,z1,z2,z4,z161,z5,z6]),(1,[z0,z1,z2,z4,z5,z162]),(0,[z0,z1,z163,z2,z4,z5,z6]),(0,[z0,z1,z2,z71,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z164,z8])],[(0,[z29,z0,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z165,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z166,z6]),(0,[z0,z1,z2,z4,z5,z8,z167])],[(0,[z40,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z168,z4,z5,z6]),(0,[z0,z1,z2,z4,z56,z5,z41]),(0,[z0,z1,z2,z4,z5,z169,z6]),(1,[z0,z70,z2,z4,z5,z90]),(0,[z0,z1,z2,z4,z5,z24,z90]),(0,[z0,z1,z2,z4,z56,z164,z6])],[(0,[z80,z1,z89,z2,z4,z5,z6]),(0,[z170,z0,z1,z2,z4,z5,z6]),(0,[z0,z140,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z171,z6])],[(1,[z93,z1,z2,z4,z28,z6]),(0,[z172,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z173,z6]),(0,[z174,z0,z1,z2,z4,z5,z8])],[(0,[z175,z0,z1,z2,z176,z5,z6])],[(0,[z0,z1,z2,z4,z5,z177,z6]),(0,[z178,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z41]),(0,[z0,z1,z2,z179,z4,z5,z6]),(0,[z180,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z181]),(1,[z0,z1,z2,z182,z5,z6]),(0,[z1,z127,z2,z14,z4,z5,z6]),(0,[z183,z0,z1,z2,z4,z5,z6]),(0,[z184,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z127,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z185,z5,z6]),(0,[z0,z1,z2,z4,z5,z186,z6]),(0,[z0,z187,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z164,z6])]],
   [[(0,[z188,z0,z1,z2,z61,z5,z6]),(0,[z72,z0,z1,z2,z4,z5,z24])],[(0,[z0,z1,z2,z4,z189,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z162])],[(1,[z0,z1,z2,z4,z5,z190]),(0,[z0,z1,z2,z4,z5,z191,z24])],[(0,[z192,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z193]),(0,[z0,z194,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z195,z6]),(1,[z0,z1,z2,z4,z5,z128]),(0,[z196,z0,z1,z2,z4,z5,z6]),(0,[z197,z0,z1,z2,z4,z5,z8]),(0,[z174,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z198]),(0,[z93,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z137,z113,z6]),(0,[z0,z1,z2,z199,z4,z5,z6]),(0,[z0,z1,z2,z132,z4,z200,z6]),(0,[z0,z1,z2,z23,z4,z20,z6])],[(0,[z114,z134,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z201,z4,z5,z6]),(0,[z0,z202,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z203,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z26,z2,z4,z20,z6]),(0,[z0,z1,z2,z4,z131,z5,z8]),(0,[z205,z0,z1,z2,z4,z5,z24]),(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z135,z4,z56,z6]),(0,[z0,z1,z207,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z208,z6]),(0,[z0,z1,z2,z209,z4,z5,z6]),(0,[z0,z1,z2,z4,z28,z113,z6]),(0,[z0,z1,z2,z4,z5,z210,z6]),(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z211,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z5,z6,z8]),(0,[z0,z1,z88,z2,z4,z5,z6]),(0,[z0,z1,z2,z212,z4,z5,z6])],[(0,[z43,z0,z2,z10,z4,z5,z6]),(0,[z213,z0,z1,z2,z4,z5,z6]),(0,[z69,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z214,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z215]),(0,[z216,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z217,z2,z4,z5,z6]),(0,[z175,z0,z1,z2,z4,z5,z218]),(0,[z0,z1,z219,z2,z4,z5,z6])],[(0,[z0,z1,z2,z220,z4,z5,z6]),(0,[z0,z1,z221,z2,z4,z5,z6]),(0,[z0,z1,z222,z2,z4,z5,z6]),(0,[z0,z223,z1,z2,z4,z5,z6]),(0,[z224,z0,z1,z2,z4,z5,z6]),(0,[z197,z0,z1,z2,z4,z5,z6])],[(0,[z114,z0,z1,z14,z4,z5,z6]),(0,[z0,z1,z2,z4,z225,z5,z6]),(1,[z0,z1,z2,z4,z5,z156]),(0,[z226,z0,z1,z2,z4,z5,z24])],[(0,[z93,z1,z2,z4,z28,z5,z6]),(0,[z0,z227,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z137,z5,z8]),(0,[z0,z1,z2,z4,z5,z6,z128]),(1,[z0,z1,z2,z71,z20,z6]),(0,[z0,z1,z2,z4,z5,z228,z24])],[(0,[z229,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z230,z5,z6]),(0,[z0,z1,z2,z231,z4,z5,z6]),(0,[z0,z1,z2,z71,z4,z20,z6]),(0,[z232,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z56,z164])],[(0,[z0,z1,z2,z4,z5,z233,z6]),(0,[z0,z1,z2,z4,z28,z5,z8]),(0,[z0,z1,z2,z234,z4,z5,z8]),(0,[z0,z1,z2,z4,z235,z5,z6])],[(0,[z236,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z237,z2,z4,z5,z6]),(0,[z238,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z8]),(0,[z239,z0,z1,z2,z4,z5,z6]),(0,[z240,z0,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z241,z5,z6]),(0,[z0,z1,z2,z4,z5,z242,z6]),(0,[z0,z1,z2,z176,z45,z5,z6]),(0,[z0,z1,z2,z243,z4,z5,z6]),(0,[z244,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z245,z2,z4,z5,z6])],[(1,[z27,z1,z2,z4,z92,z6]),(0,[z27,z0,z1,z2,z4,z92,z6]),(0,[z246,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z247,z6]),(1,[z0,z1,z2,z248,z5,z6]),(0,[z0,z1,z249,z2,z4,z5,z6])],[(0,[z250,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z162]),(0,[z74,z0,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z135,z4,z5,z24])],[(0,[z0,z1,z2,z4,z252,z5,z6]),(0,[z253,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z254,z4,z5,z6]),(0,[z0,z51,z1,z2,z4,z137,z6]),(0,[z0,z1,z2,z4,z5,z6,z156]),(0,[z0,z1,z2,z4,z255,z5,z6])],[(1,[z0,z1,z2,z4,z256,z6]),(0,[z0,z1,z2,z4,z28,z5,z6]),(0,[z0,z1,z2,z4,z20,z28,z6]),(0,[z0,z257,z219,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z136,z6]),(1,[z0,z1,z2,z4,z5,z258]),(0,[z0,z1,z2,z234,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z259]),(0,[z0,z260,z1,z2,z4,z5,z6])],[(0,[z40,z0,z1,z2,z4,z5,z8]),(1,[z0,z1,z2,z4,z5,z261]),(0,[z0,z1,z2,z4,z262,z5,z6]),(0,[z0,z1,z2,z263,z4,z5,z6]),(0,[z42,z0,z70,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z264,z6]),(0,[z188,z0,z1,z2,z4,z5,z8]),(0,[z265,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z266,z6]),(0,[z0,z1,z2,z4,z5,z267,z8])]],
   [[(0,[z114,z1,z2,z14,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z67]),(0,[z0,z1,z2,z268,z4,z5,z6]),(0,[z0,z1,z2,z71,z23,z5,z6])],[(1,[z0,z1,z2,z4,z5,z269]),(0,[z120,z72,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z30]),(0,[z270,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z271,z5,z6]),(0,[z0,z1,z2,z4,z272,z5,z6]),(0,[z42,z0,z1,z2,z4,z5,z24]),(0,[z273,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z274,z6]),(0,[z0,z1,z2,z4,z275,z5,z6]),(0,[z0,z1,z2,z276,z4,z5,z6]),(1,[z0,z1,z2,z4,z200,z6]),(0,[z7,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z277,z4,z5,z6]),(0,[z0,z1,z2,z176,z4,z5,z24]),(0,[z278,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z279,z6]),(0,[z0,z280,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z281,z5,z6]),(0,[z0,z1,z2,z71,z5,z6,z8])],[(0,[z72,z0,z1,z2,z4,z5,z8]),(0,[z15,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z282,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z283,z6]),(0,[z0,z1,z2,z284,z4,z5,z6]),(1,[z0,z1,z2,z102,z5,z8]),(0,[z0,z1,z2,z4,z5,z285,z24])],[(1,[z0,z139,z2,z4,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z24]),(0,[z0,z1,z2,z4,z52,z5,z6]),(0,[z0,z286,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z287,z5,z6]),(0,[z188,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z288,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z289,z6])],[(0,[z0,z1,z2,z4,z5,z190,z6]),(0,[z0,z257,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z6,z261]),(0,[z0,z1,z2,z290,z4,z5,z6]),(0,[z0,z1,z2,z23,z5,z113,z6]),(0,[z0,z1,z2,z4,z5,z8,z8]),(0,[z0,z1,z2,z4,z5,z6,z291])]],
   [[(0,[z40,z43,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z272,z6]),(0,[z292,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z8,z90]),(0,[z293,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z294])],[(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z175,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z296,z5,z6]),(0,[z0,z257,z1,z219,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z24])],[(0,[z0,z1,z2,z4,z5,z6,z269]),(0,[z0,z1,z89,z2,z4,z5,z24]),(0,[z43,z0,z2,z4,z137,z5,z6]),(1,[z0,z1,z2,z4,z297,z6])],[(0,[z298,z0,z1,z2,z4,z5,z6]),(0,[z29,z0,z1,z2,z4,z5,z6]),(1,[z69,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z299,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z300,z6])],[(0,[z0,z1,z301,z2,z4,z5,z6]),(0,[z0,z1,z219,z4,z45,z5,z6]),(0,[z16,z0,z1,z2,z251,z5,z6]),(0,[z7,z0,z1,z2,z4,z112,z6]),(0,[z0,z1,z2,z4,z302,z5,z6])],[(0,[z0,z1,z2,z303,z4,z5,z6]),(0,[z0,z1,z2,z4,z304,z5,z6]),(0,[z0,z1,z2,z305,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z306]),(0,[z0,z1,z2,z4,z5,z307,z6]),(0,[z0,z1,z2,z4,z5,z6,z308])],[(0,[z309,z0,z1,z2,z4,z5,z6]),(0,[z310,z0,z1,z2,z4,z5,z6]),(0,[z311,z0,z1,z2,z4,z5,z6])],[(0,[z114,z0,z1,z127,z4,z5,z6]),(0,[z0,z312,z1,z2,z4,z5,z6]),(0,[z0,z1,z313,z2,z4,z5,z6]),(0,[z63,z0,z1,z88,z4,z5,z6]),(0,[z0,z1,z314,z2,z4,z5,z6]),(0,[z0,z315,z1,z2,z4,z5,z24])]],
   [[(0,[z316,z0,z1,z2,z4,z5,z6]),(0,[z40,z188,z1,z2,z4,z5,z6]),(0,[z175,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z317,z4,z5,z6]),(0,[z0,z1,z2,z4,z318,z5,z6]),(0,[z0,z1,z88,z4,z5,z6,z67]),(0,[z0,z1,z2,z4,z5,z319,z8])],[(0,[z0,z1,z2,z4,z5,z6,z320]),(1,[z0,z321,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z322,z6]),(0,[z0,z1,z2,z323,z4,z5,z6]),(1,[z0,z51,z2,z4,z137,z6]),(0,[z0,z1,z2,z324,z4,z5,z6]),(0,[z0,z1,z2,z23,z4,z113,z6]),(0,[z325,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z326,z4,z5,z6])],[(0,[z327,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z328]),(0,[z93,z0,z321,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112,z24])],[(0,[z188,z1,z2,z176,z4,z5,z6]),(0,[z0,z1,z2,z4,z92,z112,z6]),(0,[z0,z219,z2,z10,z4,z5,z6]),(0,[z0,z1,z329,z2,z4,z5,z6]),(0,[z9,z0,z1,z132,z4,z5,z6])],[(0,[z330,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z41]),(0,[z0,z1,z95,z2,z132,z5,z6]),(0,[z331,z0,z1,z2,z4,z5,z6])],[(0,[z332,z0,z1,z2,z4,z5,z6]),(0,[z333,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z334,z6]),(0,[z0,z1,z2,z335,z4,z5,z6]),(0,[z0,z1,z2,z4,z336,z5,z6]),(0,[z0,z1,z2,z135,z4,z5,z8])],[]],
   [[(0,[z337,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z132,z4,z5,z24]),(1,[z0,z1,z2,z23,z113,z6]),(1,[z0,z1,z2,z135,z4,z150])],[(0,[z175,z0,z1,z338,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z5,z6]),(0,[z339,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z340,z6])],[(0,[z0,z1,z2,z23,z4,z5,z8])],[(0,[z188,z1,z89,z2,z4,z5,z6]),(0,[z175,z188,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z341,z4,z5,z6]),(0,[z27,z93,z1,z2,z4,z5,z6]),(0,[z342,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z343,z6]),(0,[z0,z1,z117,z2,z4,z5,z6])],[(0,[z114,z0,z104,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z4,z5,z8]),(0,[z0,z1,z344,z2,z4,z5,z6]),(1,[z0,z1,z2,z276,z4,z5]),(0,[z0,z1,z2,z132,z4,z307,z6]),(0,[z345,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z113,z6,z8])],[(0,[z0,z1,z2,z4,z346,z5,z6]),(0,[z0,z1,z2,z14,z4,z5,z8]),(0,[z0,z1,z2,z132,z61,z5,z6]),(0,[z42,z0,z1,z2,z4,z5,z8]),(0,[z7,z0,z1,z4,z45,z5,z6]),(0,[z0,z1,z2,z4,z5,z113,z6]),(0,[z0,z1,z2,z347,z4,z5,z6])],[(0,[z188,z0,z1,z2,z176,z5,z6]),(0,[z42,z0,z1,z2,z4,z5,z90]),(0,[z0,z1,z2,z4,z348,z5,z6])],[(0,[z349,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z350,z6]),(1,[z15,z0,z10,z4,z5,z6]),(0,[z0,z351,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z352,z4,z5,z6]),(0,[z0,z353,z1,z2,z4,z5,z6]),(1,[z7,z0,z1,z4,z112,z6]),(0,[z0,z1,z2,z4,z354,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z67]),(0,[z0,z1,z2,z4,z5,z6,z355]),(0,[z0,z1,z2,z4,z5,z24,z356])]],
   [[(0,[z0,z1,z2,z4,z357,z5,z6]),(0,[z0,z1,z2,z4,z5,z358,z6]),(0,[z0,z1,z2,z4,z5,z359,z6]),(0,[z0,z1,z2,z4,z5,z8,z360]),(0,[z0,z1,z2,z4,z56,z5,z8]),(0,[z0,z1,z2,z4,z5,z361,z24])],[(0,[z0,z1,z2,z176,z4,z5,z320]),(0,[z362,z0,z1,z2,z4,z5,z6]),(0,[z7,z9,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z363,z5,z6]),(0,[z0,z1,z2,z23,z4,z5,z6]),(1,[z364,z0,z1,z2,z5,z24]),(0,[z0,z1,z2,z365,z4,z5,z6])],[(1,[z134,z1,z127,z4,z5,z6]),(0,[z0,z1,z2,z176,z4,z5,z366]),(0,[z0,z1,z321,z2,z4,z5,z6]),(0,[z0,z1,z26,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z367,z6]),(0,[z63,z0,z1,z2,z4,z5,z8])],[(0,[z0,z368,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z4,z5,z6]),(0,[z16,z86,z1,z2,z4,z5,z6]),(0,[z0,z70,z2,z4,z5,z6,z90]),(1,[z0,z1,z2,z132,z5,z8]),(0,[z7,z0,z1,z2,z4,z131,z6]),(1,[z0,z1,z2,z4,z369,z5])],[(0,[z0,z1,z2,z14,z4,z5,z6]),(0,[z72,z0,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z4,z5,z370,z6]),(0,[z0,z1,z2,z4,z145,z5,z6]),(0,[z371,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z24,z8])],[(0,[z0,z1,z2,z4,z5,z372,z6]),(0,[z373,z0,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z374,z6]),(1,[z196,z0,z1,z4,z5,z6]),(0,[z0,z1,z375,z2,z4,z5,z6]),(0,[z0,z376,z1,z2,z4,z5,z6])],[(0,[z43,z0,z1,z2,z4,z5,z8]),(0,[z377,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z137,z5,z53,z6]),(0,[z0,z1,z2,z4,z5,z378,z6])],[(0,[z0,z1,z2,z4,z5,z125,z41]),(0,[z379,z0,z1,z2,z4,z5,z6]),(0,[z364,z0,z1,z2,z102,z5,z6])]],
   [[(0,[z380,z0,z1,z2,z4,z5,z6]),(0,[z381,z0,z1,z2,z4,z5,z6]),(0,[z0,z257,z1,z10,z4,z5,z6]),(0,[z0,z1,z2,z4,z382,z5,z6])],[(0,[z0,z70,z1,z2,z4,z5,z8]),(0,[z0,z383,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z384,z4,z5,z6]),(0,[z0,z70,z1,z2,z4,z5,z90]),(0,[z385,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z71,z4,z5,z6])],[(0,[z371,z0,z1,z2,z4,z5,z6]),(1,[z1,z386,z2,z4,z5,z6]),(0,[z387,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z6]),(0,[z0,z1,z2,z102,z4,z5,z8])],[(0,[z0,z1,z2,z4,z388,z5,z6]),(1,[z0,z1,z87,z4,z5,z6])],[(0,[z43,z0,z1,z2,z4,z5,z6]),(1,[z80,z89,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z167]),(0,[z63,z0,z1,z4,z5,z125,z6])],[(0,[z0,z1,z2,z4,z5,z389,z6]),(0,[z0,z1,z2,z4,z390,z5,z6]),(0,[z0,z1,z2,z4,z5,z391,z6]),(1,[z0,z1,z2,z4,z5,z24])],[(0,[z0,z1,z2,z4,z392,z5,z6]),(0,[z0,z1,z2,z4,z393,z5,z6])]],
   [[(0,[z114,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z131,z28,z6]),(0,[z0,z1,z2,z4,z5,z6,z394]),(1,[z0,z1,z2,z5,z113,z8]),(0,[z0,z1,z2,z4,z4,z5,z8])],[(0,[z0,z1,z2,z4,z5,z6,z395])],[(0,[z396,z0,z1,z2,z4,z5,z6]),(0,[z397,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z398,z6]),(0,[z0,z1,z2,z4,z5,z399,z6]),(1,[z0,z1,z2,z4,z307,z6])],[(0,[z0,z1,z2,z4,z5,z400,z6]),(0,[z16,z140,z1,z2,z4,z5,z6]),(0,[z401,z0,z1,z2,z4,z5,z6])],[(0,[z0,z402,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z403]),(0,[z0,z1,z2,z4,z404,z5,z6]),(0,[z0,z1,z2,z4,z5,z405,z6]),(0,[z0,z1,z2,z4,z5,z6,z406]),(0,[z0,z1,z2,z132,z4,z5,z8]),(0,[z63,z0,z1,z2,z135,z4,z5]),(0,[z0,z1,z2,z4,z5,z407,z6]),(0,[z0,z1,z2,z135,z4,z5,z164]),(0,[z0,z1,z2,z4,z164,z6,z150])],[(0,[z0,z1,z2,z4,z408,z5,z6]),(0,[z0,z1,z409,z2,z4,z5,z6]),(0,[z0,z1,z386,z2,z4,z5,z6]),(0,[z0,z1,z95,z2,z4,z5,z8]),(0,[z0,z1,z2,z5,z24,z6,z8])],[(0,[z0,z1,z2,z135,z4,z5,z30]),(0,[z410,z0,z1,z2,z4,z5,z6])],[(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z411]),(0,[z0,z1,z2,z4,z131,z5,z6]),(0,[z0,z1,z2,z83,z135,z5,z6]),(0,[z0,z1,z2,z4,z5,z412,z6])]],
   [[(0,[z0,z1,z2,z413,z4,z5,z6]),(0,[z0,z1,z2,z4,z414,z5,z6])],[(0,[z0,z1,z2,z4,z5,z415,z6]),(0,[z0,z1,z416,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z20,z92,z6]),(1,[z0,z1,z2,z354,z5,z6])],[],[(0,[z80,z0,z1,z2,z4,z5,z269]),(0,[z0,z1,z2,z417,z4,z5,z6]),(0,[z0,z2,z4,z5,z121,z6,z90]),(0,[z418,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z95,z2,z4,z5,z6]),(0,[z419,z0,z1,z2,z4,z5,z6]),(0,[z0,z420,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z121,z41]),(0,[z0,z1,z2,z4,z421,z5,z6]),(0,[z0,z1,z2,z4,z5,z422,z6]),(0,[z0,z1,z2,z423,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z92,z24]),(0,[z0,z194,z1,z2,z145,z5,z6]),(0,[z0,z1,z2,z4,z137,z5,z6]),(1,[z0,z1,z2,z5,z24,z8]),(0,[z0,z1,z2,z4,z56,z5,z164]),(0,[z424,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z425,z6]),(0,[z0,z1,z2,z4,z20,z137,z6]),(0,[z364,z0,z1,z2,z45,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z56,z5,z30]),(0,[z86,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z4,z5,z6]),(0,[z0,z1,z426,z2,z4,z5,z6]),(0,[z0,z1,z71,z427,z4,z5,z6])],[(0,[z428,z0,z1,z2,z4,z5,z6]),(0,[z429,z0,z1,z2,z4,z5,z6]),(0,[z430,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z431,z8])],[(0,[z43,z1,z89,z2,z4,z5,z6]),(0,[z0,z432,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z433,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z434,z6]),(1,[z0,z1,z427,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z164])],[(0,[z435,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z436,z4,z5,z6]),(0,[z0,z1,z2,z87,z4,z5,z6]),(0,[z0,z1,z437,z2,z4,z5,z6]),(0,[z0,z1,z26,z2,z4,z131,z6])],[(0,[z0,z1,z438,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z439,z6])],[(1,[z0,z1,z95,z45,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z24]),(0,[z364,z0,z1,z2,z71,z5,z6])],[(0,[z0,z1,z127,z2,z4,z5,z8]),(0,[z0,z1,z2,z440,z4,z5,z6]),(0,[z441,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z442,z5,z6]),(0,[z0,z443,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z444,z4,z5,z6]),(0,[z0,z1,z2,z4,z445,z5,z6]),(0,[z63,z0,z1,z2,z4,z56,z5])]],
   [[(0,[z40,z0,z1,z2,z4,z5,z6]),(0,[z175,z0,z98,z2,z4,z5,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z447,z6]),(0,[z0,z1,z2,z71,z4,z5,z359])],[(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z28,z5,z92,z6]),(0,[z0,z1,z2,z4,z5,z30,z8]),(0,[z0,z1,z2,z4,z449,z5,z6]),(0,[z0,z1,z2,z4,z5,z267,z6])],[(0,[z450,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z109,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z28,z112,z6]),(0,[z0,z1,z2,z4,z5,z30,z90]),(0,[z15,z0,z257,z2,z4,z5,z6]),(0,[z0,z194,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z451,z6]),(0,[z0,z1,z2,z4,z5,z452,z6]),(0,[z0,z1,z2,z4,z5,z6,z453]),(1,[z0,z1,z2,z4,z5,z8]),(0,[z364,z0,z1,z2,z4,z5,z24])],[(0,[z175,z0,z1,z109,z4,z5,z6]),(0,[z93,z0,z1,z2,z4,z5,z8]),(0,[z454,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z455,z5,z6]),(0,[z0,z1,z2,z4,z5,z456,z6])],[(1,[z0,z1,z2,z4,z5,z320]),(0,[z0,z1,z2,z4,z5,z457,z6]),(0,[z0,z51,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z20,z53,z6])],[(0,[z0,z1,z127,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z366]),(0,[z0,z1,z2,z4,z458,z5,z6])],[(0,[z459,z0,z1,z2,z4,z5,z6]),(1,[z460,z0,z2,z4,z5,z6]),(0,[z72,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z251,z4,z145,z5,z6]),(0,[z0,z1,z2,z102,z5,z6,z8])],[(0,[z0,z1,z461,z2,z4,z5,z6]),(0,[z0,z462,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z191,z6]),(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z0,z1,z463,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z464,z6])],[(0,[z465,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z466,z6]),(0,[z175,z0,z1,z2,z4,z5,z123]),(0,[z0,z1,z2,z4,z5,z53,z24])],[(0,[z467,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z132,z176,z5,z6]),(0,[z0,z1,z2,z4,z5,z403,z6]),(0,[z0,z1,z2,z4,z468,z5,z6]),(0,[z0,z1,z88,z2,z248,z5,z6]),(0,[z0,z1,z2,z248,z4,z5,z6]),(0,[z364,z0,z1,z2,z5,z113,z6]),(0,[z0,z1,z2,z4,z5,z6,z8])],[(0,[z0,z1,z2,z4,z469,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z90]),(0,[z0,z1,z2,z4,z5,z258,z6]),(0,[z0,z1,z2,z4,z5,z8,z470])],[(0,[z0,z1,z2,z4,z471,z5,z6]),(0,[z0,z472,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z473,z4,z5,z6]),(0,[z0,z1,z2,z23,z4,z5,z84])],[(0,[z474,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z125])],[(0,[z475,z0,z1,z2,z4,z5,z6]),(0,[z40,z0,z89,z2,z4,z5,z6]),(0,[z476,z0,z1,z2,z4,z5,z6]),(0,[z72,z0,z477,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z478,z6]),(0,[z16,z0,z1,z2,z4,z136,z6]),(0,[z42,z0,z1,z2,z4,z5,z121]),(0,[z0,z1,z2,z132,z5,z6,z8])]],
   [[(0,[z479,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z261]),(0,[z0,z1,z2,z4,z5,z480,z6])],[(0,[z175,z0,z1,z2,z4,z153,z6]),(0,[z0,z1,z2,z481,z4,z5,z6]),(0,[z1,z2,z4,z5,z30,z6,z41]),(0,[z0,z1,z482,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z427,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z355]),(0,[z226,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z14,z4,z45,z5,z6]),(0,[z0,z1,z2,z4,z5,z366,z6]),(0,[z0,z1,z2,z4,z5,z483,z6]),(0,[z0,z1,z2,z4,z5,z228,z6]),(0,[z0,z1,z2,z4,z5,z484,z6])],[(0,[z0,z51,z2,z4,z137,z5,z6]),(0,[z0,z51,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z485,z4,z5,z6]),(0,[z0,z486,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z20,z5,z24]),(0,[z0,z1,z2,z4,z5,z8,z150]),(0,[z0,z1,z2,z4,z5,z319,z6])],[(0,[z0,z1,z2,z4,z5,z487,z6]),(1,[z29,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z488,z4,z5,z6]),(0,[z0,z1,z489,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z369,z5,z112]),(0,[z0,z1,z2,z4,z5,z490,z6]),(0,[z0,z1,z2,z4,z5,z24,z67]),(0,[z0,z1,z2,z4,z5,z24,z491]),(0,[z0,z1,z2,z4,z5,z492,z6])],[(0,[z493,z0,z1,z2,z4,z5,z6]),(0,[z29,z72,z1,z2,z4,z5,z6]),(0,[z15,z0,z1,z219,z4,z5,z6]),(0,[z0,z1,z494,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z24])],[(0,[z27,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z495,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z121])],[(0,[z0,z1,z2,z4,z5,z6,z496]),(0,[z0,z1,z2,z4,z5,z6,z497]),(0,[z0,z498,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z194,z89,z2,z4,z5,z6]),(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z500,z4,z5,z6]),(1,[z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z5,z24]),(0,[z0,z1,z2,z4,z5,z501,z6]),(0,[z0,z502,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z135,z4,z5,z6])],[(0,[z114,z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z5,z6,z503]),(0,[z0,z1,z2,z4,z504,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z505]),(0,[z81,z0,z1,z2,z4,z5,z24])],[(0,[z0,z1,z2,z176,z4,z5,z8]),(0,[z506,z0,z1,z2,z4,z5,z6]),(0,[z29,z0,z1,z2,z4,z5,z24]),(0,[z16,z0,z1,z2,z4,z272,z6])],[(0,[z507,z0,z1,z2,z4,z5,z6]),(0,[z508,z0,z1,z2,z4,z5,z6]),(0,[z0,z70,z1,z2,z4,z5,z121]),(0,[z9,z0,z1,z95,z4,z5,z6])],[(0,[z509,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z176,z4,z61,z5,z6]),(0,[z0,z1,z2,z4,z510,z5,z6]),(0,[z511,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z8])],[(0,[z0,z1,z512,z2,z4,z5,z6]),(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z125,z8])],[(0,[z0,z1,z2,z4,z514,z5,z6]),(0,[z0,z1,z10,z4,z45,z5,z6]),(0,[z0,z257,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z515,z6]),(0,[z0,z1,z103,z2,z4,z5,z24])],[(0,[z42,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z516,z4,z5,z6]),(0,[z517,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z80,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z518,z2,z4,z5,z6]),(0,[z0,z1,z127,z4,z45,z5,z6]),(0,[z519,z0,z1,z2,z4,z5,z6]),(0,[z520,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z88,z4,z5,z67])],[(0,[z0,z1,z89,z2,z4,z5,z8]),(0,[z0,z1,z2,z176,z4,z5,z6]),(0,[z0,z1,z2,z4,z521,z5,z6]),(0,[z522,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z523,z6]),(0,[z0,z1,z2,z4,z5,z524,z6]),(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z526,z2,z4,z5,z6])],[(0,[z527,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z153,z5,z6]),(0,[z0,z1,z2,z4,z528,z5,z6]),(0,[z196,z0,z1,z71,z4,z5,z6]),(0,[z0,z1,z2,z4,z56,z5,z6])],[(1,[z40,z43,z2,z4,z5,z6]),(0,[z529,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z530,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z531,z6]),(0,[z0,z1,z2,z4,z131,z92,z6]),(0,[z532,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z20,z5,z113,z6]),(0,[z0,z1,z2,z4,z5,z6,z360])],[(0,[z0,z1,z2,z4,z5,z533,z6]),(1,[z16,z0,z2,z145,z5,z6])],[(0,[z0,z1,z2,z534,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z218,z6]),(0,[z16,z0,z2,z4,z145,z5,z6]),(0,[z70,z1,z386,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z535,z5,z6]),(0,[z0,z1,z26,z2,z4,z112,z6]),(0,[z0,z1,z2,z536,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z537,z6])]],
   [[(0,[z0,z1,z89,z2,z4,z5,z6]),(0,[z0,z1,z538,z2,z4,z5,z6]),(0,[z0,z1,z539,z2,z4,z5,z6]),(0,[z18,z0,z1,z2,z4,z5,z8])],[(0,[z0,z1,z2,z540,z4,z5,z6]),(0,[z16,z0,z194,z2,z4,z5,z6]),(0,[z0,z1,z2,z71,z20,z5,z6]),(0,[z325,z0,z1,z2,z4,z5,z8])],[(0,[z42,z0,z1,z2,z135,z4,z5]),(0,[z541,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112,z8])],[(0,[z0,z1,z2,z4,z542,z5,z6]),(0,[z543,z0,z1,z2,z4,z5,z6]),(0,[z0,z70,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z544]),(0,[z0,z1,z2,z4,z545,z5,z8])],[(0,[z1,z89,z2,z4,z61,z5,z6]),(1,[z188,z1,z2,z176,z5,z6]),(0,[z0,z1,z2,z4,z546,z5,z6]),(0,[z0,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z547,z4,z5,z6]),(0,[z0,z1,z2,z4,z56,z5,z150])],[(0,[z0,z1,z2,z548,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z218]),(0,[z0,z1,z2,z4,z92,z113,z6]),(0,[z0,z315,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z6])],[(0,[z42,z0,z89,z2,z4,z5,z6]),(1,[z0,z257,z219,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z549]),(0,[z0,z51,z1,z2,z4,z5,z8]),(0,[z0,z1,z550,z2,z4,z5,z6])]],
   [[(0,[z325,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z113,z6]),(0,[z0,z1,z2,z4,z5,z551,z6]),(0,[z552,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z150])],[(0,[z0,z1,z2,z4,z5,z553,z6]),(1,[z0,z104,z2,z4,z5,z6]),(0,[z134,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z554,z6]),(0,[z555,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112,z6]),(0,[z0,z556,z1,z2,z4,z5,z6])],[(0,[z114,z0,z129,z2,z4,z5,z6]),(0,[z0,z1,z2,z557,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z558,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z8]),(0,[z0,z1,z559,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z545,z5,z6])],[(0,[z0,z1,z560,z2,z4,z5,z6]),(0,[z561,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z145,z5,z24]),(0,[z0,z1,z2,z276,z4,z5,z53]),(0,[z0,z1,z2,z4,z5,z121,z8]),(0,[z0,z562,z1,z2,z4,z5,z6])],[(0,[z0,z257,z89,z2,z4,z5,z6]),(0,[z15,z0,z1,z10,z4,z5,z6]),(0,[z0,z1,z2,z563,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z564,z6])],[(1,[z0,z1,z2,z4,z5,z565]),(0,[z566,z0,z1,z2,z4,z5,z6]),(0,[z567,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z26,z4,z5,z6])],[(0,[z74,z0,z89,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z568,z5,z6]),(0,[z0,z1,z569,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z570]),(0,[z0,z70,z1,z2,z135,z4,z5]),(0,[z0,z1,z2,z132,z4,z5,z6]),(0,[z0,z1,z2,z4,z200,z5,z6]),(0,[z0,z571,z1,z2,z4,z5,z8]),(0,[z0,z1,z572,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z573,z6]),(0,[z0,z1,z2,z4,z5,z574,z6]),(0,[z0,z1,z2,z4,z575,z5,z6]),(0,[z0,z1,z2,z4,z382,z5,z24])]],
   [[(0,[z460,z93,z0,z2,z4,z5,z6]),(0,[z0,z1,z576,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z577,z6])],[(0,[z175,z0,z139,z2,z4,z5,z6]),(0,[z0,z1,z578,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z125,z6,z67]),(0,[z0,z1,z2,z4,z5,z8,z105])],[(0,[z0,z1,z2,z4,z579,z5,z6]),(0,[z0,z1,z580,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z121,z6]),(0,[z0,z1,z2,z4,z5,z8,z67])],[(0,[z29,z0,z1,z2,z4,z5,z41]),(0,[z15,z0,z2,z10,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z581,z6]),(0,[z0,z1,z2,z4,z5,z6,z34]),(0,[z0,z1,z2,z4,z5,z582,z6]),(0,[z0,z1,z2,z583,z4,z5,z6]),(0,[z0,z1,z2,z4,z584,z5,z6])],[(0,[z0,z1,z2,z4,z5,z125,z30]),(0,[z0,z585,z1,z2,z4,z5,z6]),(0,[z42,z0,z1,z2,z4,z56,z5]),(0,[z0,z571,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z586,z6]),(0,[z175,z0,z1,z2,z4,z297,z6]),(0,[z0,z1,z2,z4,z5,z41,z90]),(0,[z0,z1,z587,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z361,z6]),(0,[z0,z1,z2,z4,z588,z5,z6])],[(0,[z0,z589,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z369,z5,z6]),(0,[z590,z0,z1,z2,z4,z5,z6]),(0,[z206,z0,z1,z2,z4,z5,z24])]],
   [[(0,[z16,z0,z1,z2,z4,z5,z24]),(0,[z42,z0,z2,z4,z5,z121,z6]),(0,[z0,z1,z2,z591,z4,z5,z6])],[(0,[z364,z0,z1,z2,z132,z5,z6]),(0,[z0,z1,z2,z592,z4,z5,z6])],[(0,[z114,z0,z1,z2,z182,z5,z6]),(0,[z0,z1,z2,z4,z182,z5,z6]),(0,[z9,z0,z1,z4,z131,z5,z6]),(0,[z0,z1,z2,z593,z4,z5,z6]),(0,[z0,z1,z2,z4,z594,z5,z6])],[(0,[z175,z1,z2,z4,z61,z5,z6]),(0,[z595,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z596,z4,z5,z6]),(0,[z0,z1,z219,z2,z4,z5,z24]),(0,[z0,z1,z597,z2,z4,z5,z6]),(0,[z0,z1,z2,z598,z4,z5,z6]),(0,[z0,z1,z2,z4,z599,z5,z6]),(0,[z0,z1,z2,z4,z5,z600,z6]),(0,[z0,z1,z2,z4,z5,z431,z6])],[(1,[z9,z0,z1,z132,z5,z6]),(0,[z0,z601,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z602,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z491,z6])],[(0,[z114,z0,z1,z2,z4,z5,z190]),(0,[z9,z0,z1,z2,z45,z5,z6]),(0,[z603,z0,z1,z2,z4,z5,z6]),(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z537])],[(0,[z0,z1,z2,z4,z5,z605,z6]),(0,[z134,z1,z127,z2,z4,z5,z6]),(0,[z93,z0,z1,z2,z4,z28,z6]),(0,[z16,z0,z1,z2,z4,z5,z403]),(1,[z0,z1,z2,z4,z5,z399]),(0,[z0,z1,z2,z4,z131,z5,z24]),(0,[z0,z1,z2,z4,z5,z6,z84])],[(0,[z606,z0,z1,z2,z4,z5,z6]),(0,[z607,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z608,z2,z4,z5,z6]),(0,[z609,z0,z1,z2,z4,z5,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z611,z6])],[(0,[z0,z1,z2,z4,z5,z565,z6]),(0,[z0,z1,z2,z4,z612,z5,z6]),(0,[z460,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z613,z6]),(0,[z0,z1,z614,z2,z4,z5,z6]),(0,[z0,z1,z2,z615,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z616,z6]),(0,[z0,z70,z1,z2,z4,z56,z5]),(0,[z63,z0,z1,z2,z4,z5,z125])],[(0,[z43,z80,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z30,z6]),(0,[z0,z1,z88,z2,z354,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z125]),(0,[z0,z1,z2,z617,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z618,z5,z6]),(0,[z0,z194,z1,z2,z4,z5,z6]),(0,[z619,z0,z1,z2,z4,z5,z6])],[(0,[z93,z0,z1,z2,z4,z5,z6]),(0,[z0,z620,z1,z2,z4,z5,z6])],[(0,[z205,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z621]),(0,[z0,z1,z2,z4,z622,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z76])],[(0,[z0,z1,z2,z4,z5,z264,z6]),(0,[z0,z1,z2,z623,z4,z5,z6]),(0,[z93,z0,z1,z2,z4,z5,z621]),(0,[z0,z1,z2,z4,z28,z5,z24])]],
   [[(0,[z624,z0,z1,z2,z4,z5,z6]),(0,[z0,z625,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z145,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z4,z131,z5,z112,z6])],[(0,[z0,z89,z2,z10,z4,z5,z6]),(0,[z0,z1,z98,z2,z4,z5,z6]),(0,[z626,z0,z1,z2,z4,z5,z6]),(0,[z627,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z628])],[(0,[z0,z89,z2,z4,z145,z5,z6]),(0,[z629,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z1,z219,z4,z5,z6]),(0,[z0,z1,z95,z4,z45,z5,z6])],[(0,[z114,z0,z1,z2,z241,z5,z6]),(0,[z134,z0,z1,z14,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z123]),(0,[z93,z0,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z5,z121,z30]),(0,[z0,z1,z2,z4,z630,z5,z6])],[],[(1,[z0,z1,z338,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z631,z6]),(0,[z0,z1,z2,z4,z5,z92,z8]),(1,[z0,z477,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z63,z0,z1,z2,z4,z5,z67]),(0,[z0,z1,z2,z4,z5,z632,z6]),(0,[z0,z1,z2,z23,z4,z5,z108]),(0,[z0,z1,z633,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z634,z0,z1,z2,z4,z5,z6]),(0,[z635,z0,z1,z2,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z5,z24]),(0,[z0,z194,z2,z251,z4,z5,z6]),(0,[z0,z1,z2,z4,z636,z5,z6]),(0,[z0,z1,z637,z2,z4,z5,z6])],[(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z621]),(0,[z0,z1,z2,z639,z4,z5,z6]),(0,[z640,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z641,z4,z5,z6]),(0,[z40,z43,z0,z2,z4,z5,z6]),(0,[z114,z0,z1,z2,z4,z256,z6]),(0,[z0,z1,z2,z4,z256,z5,z6]),(0,[z642,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z643,z4,z5,z6]),(0,[z188,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z6,z470]),(0,[z0,z1,z2,z4,z5,z644,z6]),(0,[z0,z1,z2,z4,z645,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z646]),(0,[z0,z1,z2,z4,z5,z647,z6])],[(0,[z0,z1,z2,z648,z4,z5,z6]),(1,[z72,z1,z2,z4,z5,z41])],[(0,[z114,z0,z1,z2,z4,z264,z6]),(0,[z0,z1,z649,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z297,z6]),(0,[z0,z1,z2,z4,z5,z650,z6])],[(0,[z651,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z652,z4,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z129,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z653]),(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z654,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z655,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z8]),(0,[z656,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z8]),(0,[z364,z0,z1,z2,z5,z24,z6]),(0,[z657,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z658,z5,z6]),(0,[z0,z1,z95,z2,z4,z5,z258]),(0,[z0,z1,z2,z659,z4,z5,z6])],[(0,[z0,z1,z2,z4,z660,z5,z6]),(0,[z661,z0,z1,z2,z4,z5,z6]),(0,[z662,z0,z1,z2,z4,z5,z6]),(0,[z663,z0,z1,z2,z4,z5,z6]),(0,[z0,z664,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z665,z5,z6]),(0,[z0,z1,z2,z4,z5,z666,z6]),(0,[z0,z1,z219,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z6,z667]),(0,[z0,z1,z2,z135,z57,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z150])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z668]),(0,[z0,z1,z2,z251,z4,z5,z399]),(0,[z0,z1,z2,z4,z669,z5,z6]),(0,[z0,z1,z2,z670,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z108,z6])],[(1,[z120,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z671,z6]),(0,[z364,z0,z1,z2,z4,z5,z8])],[(0,[z175,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z672,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z673]),(0,[z74,z0,z1,z2,z4,z137,z6]),(0,[z0,z1,z2,z4,z5,z356,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z674,z4,z5,z6]),(0,[z675,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z676,z5,z6])],[(0,[z0,z1,z2,z4,z677,z5,z6]),(0,[z0,z1,z2,z4,z678,z5,z6]),(0,[z0,z1,z2,z71,z4,z5,z355])],[(0,[z679,z0,z1,z2,z4,z5,z6]),(0,[z43,z0,z2,z4,z145,z5,z6]),(0,[z680,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z477,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z285,z6]),(0,[z0,z1,z2,z135,z4,z5,z150])],[(0,[z0,z1,z681,z2,z4,z5,z6]),(0,[z0,z1,z682,z2,z4,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z6]),(0,[z0,z1,z26,z4,z131,z5,z6])],[(1,[z175,z1,z2,z61,z5,z6]),(0,[z175,z0,z1,z2,z61,z5,z6]),(0,[z683,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z132,z4,z5,z75]),(0,[z0,z1,z2,z4,z5,z125,z6]),(0,[z0,z1,z2,z4,z5,z684,z8])]],
   [[(0,[z43,z0,z194,z2,z4,z5,z6]),(0,[z0,z1,z2,z685,z4,z5,z6]),(0,[z0,z257,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z686,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z53,z8]),(0,[z7,z0,z1,z2,z4,z113,z6]),(0,[z364,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z687,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z688,z5,z6]),(0,[z0,z1,z2,z4,z689,z5,z6])],[(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z691,z4,z5,z6]),(0,[z0,z692,z1,z2,z4,z5,z6]),(0,[z0,z194,z1,z2,z251,z5,z6]),(0,[z74,z0,z51,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z693,z5,z6]),(1,[z0,z1,z2,z4,z5,z359])],[(0,[z694,z0,z1,z2,z4,z5,z6]),(0,[z1,z89,z2,z4,z5,z6,z41]),(0,[z695,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z5,z24]),(0,[z696,z0,z1,z2,z4,z5,z6])],[(0,[z0,z89,z2,z4,z137,z5,z6]),(0,[z0,z1,z2,z338,z4,z5,z6]),(0,[z0,z1,z2,z45,z61,z5,z6]),(0,[z0,z1,z2,z697,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z698,z6]),(0,[z0,z1,z2,z4,z699,z5,z6])],[(0,[z0,z1,z2,z241,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z700,z6]),(0,[z0,z1,z2,z4,z5,z701,z6]),(0,[z702,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z703,z2,z4,z5,z6]),(0,[z43,z0,z257,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z704,z5,z6]),(0,[z705,z0,z1,z2,z4,z5,z6]),(0,[z0,z706,z1,z2,z4,z5,z6]),(0,[z0,z1,z88,z2,z135,z4,z5]),(0,[z0,z1,z2,z4,z5,z684,z6])],[(0,[z80,z0,z1,z2,z4,z5,z565]),(0,[z134,z0,z1,z127,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z113,z24])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z42,z0,z2,z4,z5,z121]),(0,[z0,z1,z2,z4,z707,z5]),(0,[z0,z1,z2,z4,z307,z156]),(0,[z0,z1,z2,z132,z200,z8]),(0,[z0,z1,z2,z57,z5,z8]),(0,[z226,z0,z1,z2,z4,z76])],[(0,[z0,z1,z2,z4,z5,z708]),(0,[z0,z1,z2,z4,z5,z709]),(0,[z0,z1,z2,z4,z5,z123]),(0,[z0,z98,z338,z4,z5,z6]),(0,[z0,z710,z2,z4,z5,z6]),(0,[z63,z0,z1,z4,z5,z125])],[(0,[z0,z1,z2,z4,z711,z6]),(0,[z0,z1,z2,z4,z153,z8]),(0,[z1,z2,z4,z5,z712,z6]),(0,[z0,z1,z2,z4,z5,z713]),(0,[z16,z0,z2,z145,z136,z6]),(0,[z0,z1,z2,z248,z5,z24]),(0,[z0,z1,z4,z5,z714,z6]),(0,[z0,z1,z2,z5,z8,z76])],[(0,[z0,z129,z2,z4,z5,z6]),(0,[z114,z1,z14,z4,z5,z8]),(0,[z1,z127,z715,z4,z5,z6]),(0,[z188,z98,z2,z4,z5,z6]),(0,[z16,z0,z2,z145,z5,z261]),(0,[z74,z0,z2,z4,z53,z8]),(0,[z0,z1,z26,z2,z113,z8])],[(0,[z86,z1,z17,z4,z5,z6]),(0,[z0,z1,z87,z4,z136,z6]),(0,[z716,z0,z2,z4,z5,z8]),(0,[z0,z1,z2,z5,z24,z717])],[(0,[z718,z89,z2,z4,z5,z6]),(0,[z140,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z719]),(0,[z0,z1,z2,z4,z5,z621]),(0,[z0,z1,z2,z720,z4,z6]),(0,[z0,z1,z2,z4,z5,z721]),(0,[z0,z1,z87,z4,z5,z261]),(0,[z0,z1,z2,z45,z5,z8]),(0,[z0,z1,z2,z5,z24,z611])],[(0,[z0,z1,z2,z722,z5,z6]),(1,[z1,z2,z723,z5,z6]),(0,[z460,z0,z2,z4,z5,z155]),(0,[z0,z1,z724,z4,z5,z6]),(0,[z725,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z4,z124,z6]),(0,[z0,z571,z2,z4,z5,z470]),(0,[z0,z2,z4,z5,z8,z726])],[(0,[z0,z1,z727,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z728]),(0,[z0,z1,z2,z729,z5,z6]),(0,[z0,z1,z2,z45,z5,z320]),(0,[z730,z0,z1,z4,z5,z6]),(0,[z0,z1,z572,z132,z5,z6]),(0,[z0,z1,z2,z57,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z731]),(0,[z0,z1,z2,z33,z732,z5]),(1,[z0,z1,z4,z5,z714]),(0,[z0,z1,z427,z4,z5,z24])],[(0,[z0,z104,z2,z241,z5,z6]),(0,[z0,z1,z2,z4,z5,z733]),(0,[z0,z1,z2,z4,z5,z155]),(0,[z93,z1,z2,z4,z28,z8]),(0,[z42,z386,z2,z4,z5,z6])],[(0,[z114,z1,z14,z4,z5,z6]),(0,[z134,z1,z715,z4,z5,z6]),(0,[z0,z1,z338,z4,z5,z123]),(0,[z16,z86,z2,z145,z5,z6])],[(0,[z0,z1,z95,z45,z5,z128]),(0,[z0,z1,z95,z45,z5,z24])],[(0,[z0,z1,z2,z4,z734,z6]),(0,[z0,z1,z2,z735,z5,z6]),(0,[z0,z1,z338,z4,z5,z6]),(0,[z0,z1,z2,z5,z106,z8]),(0,[z0,z51,z2,z4,z736,z6]),(0,[z0,z1,z2,z592,z5,z24])],[(0,[z0,z1,z2,z737,z4,z5]),(0,[z0,z738,z2,z4,z5,z6]),(0,[z0,z353,z219,z4,z5,z6]),(0,[z16,z0,z2,z145,z272,z6])],[(0,[z0,z104,z2,z4,z256,z6]),(0,[z0,z1,z2,z4,z739,z5])],[(0,[z0,z1,z740,z4,z5,z6]),(0,[z0,z1,z2,z392,z5,z24]),(0,[z0,z1,z87,z4,z272,z6]),(0,[z0,z1,z741,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z742])]],
   [[(0,[z0,z104,z2,z4,z264,z6]),(0,[z0,z743,z2,z4,z5,z6]),(0,[z0,z1,z744,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z745]),(0,[z0,z1,z2,z48,z5,z8]),(0,[z72,z1,z2,z4,z5,z41]),(0,[z0,z2,z4,z5,z746,z90]),(0,[z0,z1,z2,z354,z5,z125])],[(0,[z19,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z4,z747,z6]),(0,[z0,z1,z2,z4,z5,z748]),(0,[z0,z1,z2,z4,z5,z749]),(0,[z0,z1,z2,z179,z20,z6]),(0,[z0,z1,z2,z750,z4,z5])],[],[(0,[z0,z1,z2,z182,z5,z6]),(0,[z0,z1,z2,z4,z5,z751]),(0,[z175,z98,z2,z61,z5,z6])],[(0,[z0,z1,z2,z4,z5,z752]),(0,[z140,z1,z17,z4,z5,z6]),(0,[z753,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z4,z369,z112]),(0,[z364,z0,z1,z2,z5,z359]),(0,[z754,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z755,z4,z5]),(0,[z0,z1,z2,z4,z756,z5]),(0,[z635,z0,z1,z132,z5,z6]),(0,[z0,z1,z757,z4,z5,z6]),(0,[z0,z1,z103,z4,z5,z125]),(0,[z0,z1,z2,z71,z575,z6])],[(0,[z43,z567,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z190]),(0,[z175,z1,z109,z61,z5,z6]),(0,[z0,z1,z2,z4,z5,z758]),(0,[z63,z0,z1,z2,z57,z5]),(0,[z63,z0,z1,z4,z584,z5]),(0,[z196,z0,z1,z4,z5,z355]),(0,[z0,z1,z2,z4,z382,z164]),(0,[z0,z759,z2,z4,z5,z6])],[(0,[z0,z438,z2,z4,z5,z90]),(0,[z42,z0,z2,z4,z5,z605]),(0,[z0,z1,z2,z241,z5,z760]),(0,[z0,z1,z2,z4,z761,z6]),(0,[z0,z1,z2,z4,z297,z218]),(0,[z0,z1,z2,z4,z762,z6]),(0,[z763,z1,z2,z4,z5,z6])]],
   [[(0,[z197,z0,z1,z4,z5,z684])],[(0,[z0,z1,z764,z4,z5,z6]),(0,[z765,z0,z2,z4,z5,z6]),(0,[z174,z1,z2,z4,z5,z41]),(0,[z0,z70,z1,z2,z57,z5]),(0,[z0,z1,z2,z71,z20,z8])],[(0,[z0,z766,z2,z4,z5,z6]),(0,[z379,z1,z2,z4,z92,z6])],[(0,[z0,z1,z2,z4,z5,z767]),(0,[z0,z321,z2,z4,z5,z24]),(0,[z0,z51,z2,z4,z137,z24]),(0,[z768,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z769]),(0,[z0,z1,z2,z770,z4,z5]),(0,[z175,z1,z2,z61,z5,z123]),(0,[z0,z1,z2,z4,z5,z771]),(0,[z196,z0,z1,z4,z20,z6])],[(0,[z0,z1,z2,z241,z5,z8]),(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z2,z5,z773,z8]),(0,[z0,z1,z2,z4,z5,z774])],[(0,[z89,z2,z4,z5,z41,z90]),(0,[z202,z89,z2,z4,z5,z6]),(0,[z27,z1,z2,z4,z92,z8]),(0,[z0,z2,z775,z4,z5,z6]),(0,[z0,z1,z2,z248,z5,z8]),(0,[z0,z1,z2,z5,z717,z8]),(0,[z0,z1,z2,z57,z5,z164])],[(0,[z0,z1,z109,z4,z5,z218]),(0,[z0,z1,z2,z4,z5,z776]),(0,[z0,z1,z2,z122,z5,z8])]],
   [[(0,[z380,z1,z2,z61,z5,z6]),(0,[z0,z1,z2,z4,z5,z777]),(0,[z0,z1,z2,z57,z5,z30]),(0,[z0,z1,z2,z4,z778,z6]),(0,[z779,z0,z1,z4,z5,z6]),(0,[z70,z386,z2,z4,z5,z90]),(0,[z0,z1,z2,z5,z166,z8]),(0,[z0,z1,z2,z71,z20,z6]),(0,[z0,z1,z2,z326,z5,z8])],[(0,[z1,z438,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z780]),(0,[z0,z1,z2,z781,z5,z6]),(0,[z0,z1,z2,z4,z5,z782]),(0,[z0,z1,z2,z4,z5,z359])],[(0,[z0,z1,z2,z4,z783,z6]),(0,[z0,z1,z2,z4,z256,z8]),(0,[z0,z1,z2,z784,z5,z6]),(0,[z298,z0,z1,z4,z112,z6]),(0,[z0,z1,z2,z4,z136,z8]),(0,[z42,z0,z2,z4,z235,z5]),(0,[z0,z1,z2,z785,z113,z6])],[(0,[z0,z786,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z173,z8]),(0,[z0,z787,z2,z4,z5,z6])],[(0,[z0,z1,z2,z241,z5,z6]),(0,[z0,z788,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z8]),(0,[z0,z1,z2,z4,z789,z6])],[(0,[z0,z257,z301,z4,z5,z6]),(0,[z0,z1,z2,z790,z5,z6])],[(0,[z0,z1,z2,z791,z5,z6]),(0,[z0,z1,z2,z4,z792,z5]),(0,[z0,z1,z2,z185,z5,z8])],[(0,[z175,z1,z338,z61,z5,z6]),(0,[z0,z1,z2,z4,z200,z8])]],
   [[(0,[z0,z1,z2,z4,z5,z793]),(0,[z541,z1,z14,z4,z5,z6]),(0,[z794,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z795]),(0,[z0,z1,z2,z796,z5,z6]),(0,[z0,z1,z2,z135,z4,z456])],[(0,[z0,z1,z2,z4,z256,z6]),(0,[z0,z797,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z136,z6]),(0,[z0,z1,z2,z4,z5,z258]),(0,[z0,z1,z2,z798,z5,z6])],[(0,[z40,z1,z2,z4,z5,z269]),(0,[z0,z139,z2,z4,z5,z8]),(0,[z0,z799,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z800,z5])],[(0,[z801,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z6]),(0,[z0,z1,z2,z4,z5,z802]),(0,[z0,z1,z2,z137,z113,z8]),(0,[z0,z1,z2,z4,z803,z6]),(0,[z804,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z671,z8])],[(0,[z0,z1,z2,z4,z805,z6]),(0,[z0,z1,z17,z4,z5,z403]),(0,[z0,z1,z2,z806,z4,z5]),(0,[z7,z0,z1,z4,z484,z6]),(0,[z0,z1,z2,z33,z4,z5])],[(0,[z0,z1,z2,z4,z5,z269]),(0,[z0,z1,z2,z5,z807,z6]),(0,[z43,z238,z2,z4,z5,z6]),(0,[z0,z129,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z153,z218]),(0,[z0,z1,z2,z28,z113,z8]),(0,[z0,z1,z2,z4,z272,z8]),(0,[z0,z1,z2,z4,z5,z808]),(0,[z0,z1,z2,z659,z5,z8]),(0,[z64,z1,z2,z4,z5,z191]),(0,[z809,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z436,z5,z8]),(0,[z0,z1,z2,z4,z200,z6]),(0,[z0,z1,z2,z4,z5,z810]),(0,[z0,z1,z2,z4,z811,z6])],[(0,[z0,z1,z812,z4,z5,z6]),(0,[z0,z1,z2,z4,z297,z8]),(0,[z0,z1,z2,z4,z5,z813]),(0,[z0,z1,z2,z4,z5,z814]),(0,[z0,z1,z2,z4,z815,z8])]],
   [[(0,[z69,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z132,z307,z8]),(0,[z0,z1,z2,z102,z5,z8])],[(0,[z0,z1,z2,z4,z712,z6]),(0,[z16,z0,z87,z145,z5,z6]),(0,[z0,z1,z2,z4,z816,z5])],[(0,[z1,z2,z4,z712,z92,z6]),(0,[z0,z1,z2,z817,z5,z6]),(0,[z0,z1,z2,z4,z818,z6]),(0,[z63,z0,z1,z4,z5,z714])],[(0,[z0,z1,z2,z4,z5,z819]),(0,[z0,z1,z2,z4,z5,z820]),(0,[z0,z821,z2,z4,z5,z6]),(0,[z0,z98,z109,z4,z5,z6]),(0,[z16,z0,z2,z145,z5,z24]),(0,[z0,z1,z2,z132,z5,z128]),(0,[z0,z1,z4,z5,z714,z67]),(0,[z0,z1,z427,z4,z5,z355])],[(0,[z114,z1,z14,z4,z5,z34]),(0,[z0,z822,z2,z4,z5,z6]),(0,[z0,z1,z823,z4,z5,z6]),(0,[z1,z386,z2,z4,z5,z24]),(0,[z0,z1,z2,z824,z4,z5]),(0,[z0,z1,z2,z230,z5,z8]),(0,[z0,z1,z2,z234,z4,z150]),(0,[z0,z1,z2,z4,z382,z285])],[(0,[z380,z0,z1,z2,z5,z8]),(0,[z825,z1,z2,z4,z5,z6]),(0,[z0,z1,z87,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z826])],[(0,[z0,z1,z2,z4,z5,z827]),(0,[z0,z1,z2,z4,z297,z6]),(0,[z0,z1,z2,z4,z815,z6]),(0,[z0,z1,z2,z4,z5,z828])],[(0,[z69,z1,z2,z4,z5,z6]),(0,[z0,z321,z2,z4,z5,z8]),(0,[z0,z51,z2,z4,z137,z8]),(0,[z371,z1,z2,z4,z5,z267]),(0,[z0,z315,z2,z4,z5,z356])]],
   [[(0,[z0,z1,z17,z4,z136,z6]),(0,[z0,z829,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z830]),(0,[z718,z1,z2,z4,z5,z6]),(0,[z0,z98,z2,z4,z5,z123]),(0,[z0,z831,z2,z4,z5,z6]),(0,[z0,z1,z17,z4,z5,z261]),(0,[z832,z1,z2,z4,z5,z6]),(0,[z16,z0,z2,z145,z5,z403])],[(0,[z0,z1,z2,z4,z5,z833]),(0,[z0,z1,z2,z4,z5,z834]),(0,[z188,z1,z2,z176,z5,z24]),(0,[z1,z835,z2,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z431])],[(0,[z0,z1,z2,z836,z5,z6]),(0,[z0,z1,z2,z837,z5,z6]),(0,[z0,z1,z87,z4,z5,z403]),(0,[z0,z1,z2,z4,z307,z24])],[(0,[z0,z89,z2,z4,z5,z269]),(0,[z0,z1,z109,z4,z5,z123]),(0,[z0,z202,z2,z4,z5,z90]),(0,[z0,z257,z219,z4,z5,z24]),(0,[z0,z1,z2,z4,z838,z6]),(0,[z0,z1,z88,z248,z5,z67]),(0,[z0,z1,z2,z4,z5,z108]),(0,[z0,z1,z2,z57,z5,z285])],[(0,[z0,z1,z2,z182,z5,z34]),(0,[z0,z1,z2,z23,z113,z8])],[(0,[z0,z1,z2,z839,z5,z6]),(0,[z0,z840,z2,z4,z5,z6]),(0,[z345,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z5,z266,z8])],[(0,[z0,z104,z2,z4,z5,z24]),(0,[z0,z1,z338,z4,z297,z6]),(0,[z107,z1,z2,z4,z92,z6]),(0,[z0,z1,z2,z841,z5,z6]),(0,[z0,z1,z88,z4,z5,z714])]],
   [[(0,[z0,z1,z842,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z843]),(0,[z0,z844,z2,z4,z5,z6]),(0,[z29,z1,z2,z4,z5,z267])],[(0,[z0,z845,z2,z4,z5,z6]),(0,[z0,z1,z2,z846,z5,z6]),(0,[z0,z70,z2,z4,z5,z746])],[(0,[z1,z89,z2,z4,z5,z269]),(0,[z80,z89,z2,z4,z5,z565]),(0,[z847,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z848,z6]),(0,[z196,z0,z1,z4,z113,z6])],[(0,[z29,z1,z2,z4,z5,z849]),(0,[z0,z1,z17,z4,z272,z6]),(0,[z0,z1,z850,z4,z5,z6]),(0,[z0,z1,z2,z4,z851,z5])],[(0,[z638,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z852,z6]),(0,[z15,z0,z10,z4,z5,z8]),(0,[z0,z1,z2,z853,z5,z6]),(0,[z7,z0,z1,z4,z112,z8])],[(0,[z1,z854,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z855]),(0,[z0,z1,z88,z365,z4,z5]),(0,[z0,z1,z2,z83,z5,z6])],[(0,[z0,z1,z2,z4,z5,z856]),(0,[z0,z1,z2,z4,z857,z6]),(0,[z1,z2,z4,z5,z30,z849]),(0,[z1,z858,z2,z4,z5,z6]),(0,[z364,z0,z1,z2,z5,z717]),(0,[z0,z1,z103,z4,z5,z361])],[(0,[z0,z1,z2,z4,z859,z6]),(0,[z134,z1,z127,z4,z5,z8]),(0,[z9,z0,z1,z796,z5,z6]),(0,[z0,z1,z2,z324,z113,z6])]],
   [[(0,[z0,z1,z2,z860,z5,z6]),(0,[z0,z1,z2,z135,z57,z150])],[(0,[z0,z1,z2,z4,z5,z861]),(0,[z0,z1,z2,z4,z862,z6]),(0,[z0,z1,z2,z863,z5,z6]),(0,[z0,z1,z2,z4,z5,z864])],[(0,[z0,z1,z95,z796,z5,z6]),(0,[z196,z0,z1,z4,z5,z8]),(0,[z0,z1,z2,z5,z8,z308])],[(0,[z15,z0,z10,z4,z5,z6]),(0,[z0,z1,z2,z79,z5,z8]),(0,[z0,z386,z2,z4,z5,z90]),(0,[z0,z70,z2,z4,z5,z356]),(0,[z410,z0,z1,z2,z5,z24]),(0,[z7,z0,z1,z4,z112,z6]),(0,[z0,z1,z2,z865,z4,z5]),(0,[z0,z1,z2,z4,z56,z632]),(0,[z0,z1,z2,z302,z5,z8])],[(0,[z0,z1,z2,z4,z866,z6]),(0,[z0,z1,z867,z4,z5,z6]),(0,[z0,z1,z2,z4,z153,z6]),(0,[z0,z1,z614,z45,z5,z6]),(0,[z42,z0,z2,z4,z5,z431]),(0,[z0,z1,z2,z5,z307,z8])],[(0,[z114,z129,z14,z4,z5,z6]),(0,[z74,z0,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z5,z868]),(0,[z364,z0,z1,z2,z5,z24])],[(0,[z134,z1,z127,z4,z5,z6]),(0,[z0,z1,z2,z241,z5,z34]),(0,[z541,z1,z2,z61,z5,z6]),(0,[z0,z1,z2,z71,z5,z8]),(0,[z716,z0,z2,z4,z5,z6])],[(0,[z0,z1,z869,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z870]),(0,[z0,z1,z871,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z162]),(0,[z16,z0,z2,z145,z5,z8]),(0,[z0,z1,z2,z4,z369,z5]),(0,[z0,z1,z2,z324,z5,z8])]],
   [[(0,[z0,z1,z2,z4,z5,z872]),(0,[z1,z386,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z873])],[(0,[z0,z1,z2,z4,z5,z874]),(0,[z0,z1,z2,z4,z875,z6]),(0,[z175,z1,z2,z61,z297,z6]),(0,[z0,z1,z2,z132,z5,z320]),(0,[z0,z1,z2,z4,z5,z849]),(0,[z0,z1,z87,z4,z5,z8]),(0,[z1,z386,z2,z4,z5,z90]),(0,[z0,z70,z2,z4,z5,z90]),(0,[z196,z0,z1,z4,z5,z6])],[(0,[z80,z89,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z9,z0,z1,z132,z5,z24]),(0,[z0,z1,z2,z23,z785,z6]),(0,[z0,z2,z4,z5,z6,z726]),(0,[z0,z877,z2,z4,z5,z24])],[(0,[z0,z1,z2,z4,z256,z34]),(0,[z1,z2,z4,z723,z5,z6]),(0,[z93,z1,z2,z4,z28,z6]),(0,[z0,z1,z2,z4,z5,z717])],[(0,[z878,z0,z1,z2,z4,z5]),(0,[z0,z1,z715,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z879]),(0,[z0,z1,z2,z73,z5,z8]),(0,[z880,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z691,z5,z8]),(0,[z0,z1,z2,z57,z5,z150])],[(0,[z0,z1,z881,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z34]),(0,[z0,z139,z2,z4,z5,z218]),(0,[z0,z1,z338,z4,z153,z6]),(0,[z0,z1,z2,z4,z5,z882]),(0,[z93,z1,z2,z4,z28,z621]),(0,[z0,z1,z2,z4,z5,z883])],[(0,[z0,z1,z2,z4,z884,z6]),(0,[z0,z129,z2,z182,z5,z6])],[(0,[z0,z1,z2,z4,z5,z885]),(0,[z460,z0,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z307,z8]),(0,[z0,z1,z2,z427,z5,z8]),(0,[z81,z0,z1,z4,z5,z537])]],
   [[(0,[z188,z1,z2,z176,z5,z320]),(0,[z0,z1,z2,z4,z5,z886])],[(0,[z80,z89,z2,z4,z5,z6]),(0,[z0,z129,z2,z4,z5,z190]),(0,[z0,z1,z2,z4,z5,z887]),(0,[z188,z1,z2,z176,z5,z366]),(0,[z93,z1,z2,z4,z28,z155]),(0,[z0,z2,z4,z5,z746,z6])],[(0,[z0,z1,z2,z4,z5,z24]),(0,[z0,z194,z2,z251,z5,z8]),(0,[z0,z1,z2,z4,z5,z128]),(0,[z9,z0,z1,z132,z5,z156])],[(0,[z381,z0,z2,z4,z5,z90]),(0,[z0,z1,z2,z241,z5,z833]),(0,[z0,z1,z888,z4,z5,z6]),(0,[z889,z1,z2,z4,z5,z6]),(0,[z0,z1,z890,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z891]),(0,[z0,z1,z2,z135,z4,z742])],[(0,[z0,z1,z2,z182,z5,z733]),(0,[z120,z72,z2,z4,z5,z41]),(0,[z143,z0,z2,z4,z53,z6]),(0,[z892,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z113,z8])],[(0,[z114,z1,z14,z182,z5,z6]),(0,[z0,z257,z775,z4,z5,z6]),(0,[z0,z1,z4,z5,z125,z714]),(0,[z1,z893,z2,z4,z5,z24])],[(0,[z0,z1,z2,z4,z5,z894]),(0,[z86,z1,z2,z4,z136,z6]),(0,[z0,z1,z2,z354,z5,z8])],[(0,[z0,z1,z2,z5,z24,z400]),(0,[z0,z1,z2,z4,z200,z75]),(0,[z895,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z359,z8])]],
   [[(0,[z114,z1,z14,z4,z5,z190]),(0,[z0,z1,z2,z4,z5,z403]),(0,[z0,z1,z2,z896,z5,z6]),(0,[z0,z1,z2,z4,z5,z897]),(0,[z0,z1,z2,z363,z5,z8]),(0,[z63,z0,z1,z4,z5,z684]),(0,[z0,z898,z2,z4,z5,z8])],[(0,[z1,z2,z715,z4,z5,z6]),(0,[z27,z1,z2,z4,z712,z6])],[(0,[z0,z1,z2,z4,z5,z156]),(0,[z0,z1,z37,z45,z5,z6])],[(0,[z0,z1,z2,z4,z5,z899]),(0,[z0,z1,z2,z4,z5,z900]),(0,[z0,z1,z2,z4,z5,z901]),(0,[z0,z1,z338,z4,z5,z24]),(0,[z0,z477,z2,z4,z5,z24]),(0,[z0,z2,z4,z137,z736,z6]),(0,[z0,z1,z2,z4,z5,z902]),(0,[z0,z1,z2,z83,z5,z359])],[(0,[z0,z1,z903,z2,z5,z6]),(0,[z0,z1,z4,z5,z6,z904]),(0,[z0,z219,z775,z4,z5,z6]),(0,[z0,z1,z2,z284,z5,z8]),(0,[z0,z1,z2,z132,z5,z773]),(0,[z0,z1,z2,z4,z56,z164])],[(0,[z0,z1,z905,z4,z5,z6]),(0,[z906,z0,z2,z4,z5,z6]),(0,[z16,z0,z17,z145,z5,z6]),(0,[z9,z0,z1,z179,z5,z6])],[(0,[z0,z907,z2,z4,z5,z6]),(0,[z460,z93,z2,z4,z28,z6]),(0,[z0,z1,z2,z4,z56,z322]),(0,[z908,z1,z2,z4,z5,z8])],[(0,[z0,z1,z2,z909,z5,z6]),(0,[z0,z129,z2,z241,z5,z6]),(0,[z175,z1,z2,z61,z153,z6]),(0,[z0,z1,z2,z4,z5,z910]),(0,[z0,z1,z2,z4,z5,z911]),(0,[z0,z1,z427,z4,z5,z8])]],
   [[(0,[z0,z1,z2,z4,z5,z912]),(0,[z419,z1,z127,z4,z5,z6]),(0,[z27,z1,z2,z4,z92,z6]),(0,[z0,z775,z10,z4,z5,z6]),(0,[z0,z1,z2,z4,z913,z5]),(0,[z0,z1,z2,z248,z5,z6]),(0,[z0,z1,z2,z4,z5,z914]),(0,[z0,z1,z2,z4,z5,z915]),(0,[z916,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z5,z717,z6])],[(0,[z40,z595,z2,z4,z5,z6]),(0,[z0,z1,z2,z182,z5,z190]),(0,[z253,z1,z2,z4,z5,z30]),(0,[z86,z1,z2,z4,z272,z6]),(0,[z0,z1,z17,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z917]),(0,[z9,z0,z1,z132,z200,z6]),(0,[z0,z1,z2,z4,z5,z918]),(0,[z0,z1,z117,z4,z5,z67]),(0,[z0,z1,z2,z5,z24,z524])],[(0,[z0,z1,z2,z919,z4,z5]),(0,[z0,z1,z95,z45,z5,z8]),(0,[z0,z1,z2,z5,z24,z8])],[(0,[z0,z1,z2,z4,z5,z920]),(0,[z0,z1,z2,z921,z5,z6])],[(0,[z0,z129,z2,z4,z256,z6]),(0,[z0,z139,z109,z4,z5,z6]),(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z923])],[(0,[z0,z1,z2,z924,z5,z6]),(0,[z0,z1,z2,z4,z5,z261]),(0,[z0,z1,z2,z5,z391,z8])],[(0,[z0,z129,z2,z4,z264,z6]),(0,[z114,z1,z14,z241,z5,z6]),(0,[z0,z98,z2,z4,z297,z6]),(0,[z140,z1,z2,z4,z136,z6]),(0,[z925,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z56,z742])],[(0,[z0,z1,z2,z4,z5,z926]),(0,[z120,z0,z2,z4,z5,z24])]],
   [[(0,[z0,z1,z2,z732,z5,z6]),(0,[z765,z0,z2,z4,z5,z24])],[(0,[z0,z1,z109,z4,z297,z6]),(0,[z0,z1,z2,z927,z5,z6]),(0,[z0,z1,z928,z4,z5,z6]),(0,[z0,z1,z95,z45,z5,z6]),(0,[z0,z1,z796,z4,z5,z6])],[(0,[z0,z1,z2,z4,z929,z6]),(0,[z0,z139,z2,z4,z5,z123]),(0,[z0,z1,z2,z59,z5,z8])],[(0,[z0,z1,z2,z4,z5,z930]),(0,[z114,z1,z14,z4,z256,z6]),(0,[z460,z0,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z931]),(0,[z0,z1,z2,z4,z5,z932]),(0,[z933,z1,z2,z4,z5,z6]),(0,[z364,z0,z1,z427,z5,z6])],[(0,[z0,z139,z2,z4,z5,z6]),(0,[z40,z43,z2,z4,z5,z24]),(0,[z0,z1,z2,z182,z5,z780]),(0,[z0,z1,z934,z2,z4,z5]),(0,[z0,z935,z2,z4,z5,z6]),(0,[z0,z1,z2,z785,z5,z6])],[(0,[z114,z1,z14,z4,z264,z6]),(0,[z175,z1,z2,z61,z5,z24]),(0,[z74,z0,z2,z276,z4,z53])],[(0,[z0,z1,z2,z4,z936,z6]),(0,[z0,z1,z2,z4,z5,z937]),(0,[z0,z938,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z939]),(0,[z0,z1,z2,z4,z297,z123]),(0,[z0,z1,z2,z723,z5,z6]),(0,[z0,z1,z2,z4,z5,z940]),(0,[z0,z1,z2,z4,z272,z6]),(0,[z0,z1,z2,z4,z5,z941]),(0,[z0,z1,z2,z414,z5,z8])]],
   [[(0,[z0,z1,z2,z4,z5,z320]),(0,[z0,z60,z2,z4,z137,z6]),(0,[z386,z2,z4,z5,z6,z90]),(0,[z0,z1,z942,z4,z5,z6]),(0,[z0,z943,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z742])],[(0,[z0,z1,z2,z4,z944,z6]),(0,[z0,z1,z2,z4,z5,z366]),(0,[z0,z1,z2,z158,z5,z8])],[(0,[z0,z1,z2,z241,z5,z190]),(0,[z0,z1,z2,z4,z5,z945]),(0,[z946,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z732,z5])],[(1,[z718,z2,z4,z5,z6]),(0,[z0,z1,z947,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z948]),(0,[z949,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z182,z256,z6]),(0,[z519,z0,z1,z2,z5,z24]),(0,[z0,z1,z2,z421,z5,z8]),(0,[z0,z1,z88,z354,z5,z67]),(0,[z0,z1,z2,z4,z785,z6])],[(0,[z0,z1,z2,z4,z950,z6]),(0,[z0,z1,z2,z4,z5,z951]),(0,[z0,z1,z2,z4,z952,z6]),(0,[z0,z139,z338,z4,z5,z6]),(0,[z0,z953,z2,z4,z5,z6]),(0,[z0,z1,z117,z45,z5,z8]),(0,[z0,z1,z2,z4,z954,z5])],[(0,[z0,z1,z2,z182,z264,z6]),(0,[z7,z0,z1,z4,z523,z6])],[(0,[z0,z1,z2,z4,z256,z190]),(0,[z0,z1,z2,z4,z5,z955])]],
   [[(0,[z0,z1,z956,z4,z5,z6])],[(0,[z0,z321,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z190]),(0,[z0,z1,z2,z957,z5,z6]),(0,[z0,z51,z2,z4,z137,z6]),(0,[z0,z1,z2,z71,z20,z359])],[(0,[z0,z1,z2,z4,z5,z958]),(0,[z0,z1,z2,z4,z5,z959]),(0,[z0,z1,z2,z4,z5,z960]),(0,[z0,z1,z2,z4,z5,z961]),(0,[z188,z1,z2,z723,z5,z6]),(0,[z962,z1,z2,z4,z5,z6]),(0,[z0,z963,z2,z4,z5,z6])],[(0,[z0,z964,z2,z4,z5,z6]),(0,[z1,z2,z723,z61,z5,z6]),(0,[z0,z321,z2,z4,z5,z621]),(0,[z0,z2,z4,z736,z53,z6]),(0,[z0,z1,z2,z4,z965,z5])],[(0,[z0,z1,z2,z4,z5,z966]),(0,[z0,z98,z2,z4,z153,z6]),(0,[z0,z477,z2,z4,z5,z41]),(0,[z0,z1,z2,z234,z113,z8])],[(0,[z1,z2,z176,z723,z5,z6]),(0,[z0,z1,z2,z4,z967,z6]),(0,[z140,z2,z4,z145,z5,z6]),(0,[z0,z1,z17,z4,z5,z8]),(0,[z69,z70,z2,z4,z5,z90]),(0,[z0,z1,z2,z670,z5,z8]),(0,[z0,z1,z2,z4,z5,z355])],[(0,[z0,z1,z21,z2,z5,z8]),(0,[z72,z1,z2,z4,z5,z491]),(0,[z968,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z45,z5,z8])],[(0,[z0,z1,z109,z4,z153,z6]),(0,[z0,z1,z2,z23,z113,z6]),(0,[z0,z1,z2,z135,z4,z150])]],
   [[(0,[z705,z89,z2,z4,z5,z6]),(0,[z93,z1,z2,z4,z712,z6]),(0,[z29,z1,z2,z4,z5,z30]),(0,[z140,z194,z2,z4,z5,z6]),(0,[z74,z0,z2,z4,z736,z6]),(0,[z0,z1,z2,z732,z5,z112]),(0,[z969,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z970,z5,z6]),(0,[z0,z1,z2,z971,z5,z6]),(0,[z0,z1,z2,z71,z5,z84])],[(0,[z1,z477,z2,z4,z5,z41]),(0,[z229,z1,z2,z4,z5,z41]),(0,[z1,z386,z2,z4,z5,z121]),(0,[z0,z1,z2,z455,z5,z8]),(0,[z0,z1,z427,z5,z6,z8])],[(0,[z0,z1,z2,z4,z972,z6]),(0,[z0,z1,z2,z4,z5,z973]),(0,[z0,z1,z2,z276,z4,z5]),(0,[z0,z1,z2,z4,z5,z773])],[(0,[z0,z1,z14,z182,z5,z6]),(0,[z0,z1,z974,z4,z5,z6]),(0,[z0,z1,z4,z45,z200,z6])],[(0,[z0,z1,z2,z241,z256,z6]),(0,[z0,z1,z2,z975,z5,z6]),(0,[z0,z1,z2,z4,z153,z123]),(0,[z0,z1,z2,z135,z4,z215])],[(0,[z694,z89,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z976,z6]),(0,[z977,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z158,z20,z6])],[(0,[z40,z187,z2,z4,z5,z6]),(0,[z0,z1,z2,z241,z264,z6]),(0,[z175,z139,z2,z61,z5,z6]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z86,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z979]),(0,[z42,z0,z1,z2,z57,z5]),(0,[z0,z2,z4,z5,z980,z6]),(0,[z311,z0,z1,z2,z5,z8]),(0,[z969,z0,z1,z2,z33,z5])]],
   [[(0,[z40,z43,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z981]),(0,[z0,z1,z2,z4,z5,z982]),(0,[z0,z1,z2,z4,z983,z6]),(0,[z0,z1,z2,z984,z4,z5]),(0,[z0,z1,z199,z45,z5,z6]),(0,[z1,z2,z4,z5,z985,z6]),(0,[z9,z0,z1,z4,z200,z6])],[(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z1,z987,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z988]),(0,[z0,z98,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z989]),(0,[z0,z1,z2,z132,z5,z8])],[],[(0,[z0,z1,z2,z4,z5,z990]),(0,[z0,z2,z4,z5,z736,z6]),(0,[z0,z1,z2,z991,z5,z6]),(1,[z0,z1,z796,z5,z6]),(0,[z364,z0,z1,z2,z307,z6])],[(0,[z0,z1,z109,z4,z5,z24]),(0,[z0,z1,z2,z384,z5,z8]),(0,[z0,z1,z2,z4,z992,z5]),(0,[z86,z1,z2,z4,z5,z403]),(0,[z0,z1,z2,z4,z993,z6]),(0,[z0,z1,z2,z299,z5,z8])],[(0,[z590,z1,z2,z4,z28,z6]),(0,[z0,z1,z2,z254,z5,z24]),(0,[z0,z1,z2,z4,z5,z994]),(0,[z0,z1,z2,z4,z995,z6])],[(0,[z74,z0,z2,z4,z439,z6]),(0,[z9,z0,z1,z436,z5,z6]),(0,[z0,z1,z2,z4,z996,z6]),(0,[z0,z1,z2,z5,z113,z84])]],
   [[(0,[z0,z1,z997,z2,z5,z6]),(0,[z0,z1,z2,z4,z998,z6]),(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z1,z2,z4,z5,z1000]),(0,[z0,z1001,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1002]),(0,[z0,z1,z1003,z4,z5,z6]),(0,[z188,z1,z2,z176,z5,z8]),(0,[z16,z0,z2,z145,z5,z6]),(0,[z0,z1,z2,z4,z1004,z5]),(0,[z0,z1,z2,z5,z484,z8]),(0,[z9,z0,z1,z132,z307,z6]),(0,[z0,z1,z2,z248,z5,z75])],[(0,[z1,z386,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1005,z5]),(0,[z205,z1,z2,z4,z5,z491])],[(0,[z0,z1,z87,z4,z5,z6]),(0,[z0,z257,z219,z4,z5,z8]),(0,[z0,z1,z2,z4,z1006,z6]),(0,[z0,z1,z2,z5,z492,z8])],[(0,[z1007,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z1008]),(0,[z0,z1,z2,z307,z6,z8]),(0,[z0,z1,z2,z4,z5,z714]),(0,[z196,z0,z1,z71,z5,z8]),(0,[z0,z1,z2,z83,z5,z24]),(0,[z0,z1,z2,z4,z164,z742])],[(0,[z0,z129,z2,z4,z5,z24]),(0,[z0,z1,z1009,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1010]),(1,[z0,z1,z2,z5,z717])],[(0,[z178,z89,z2,z4,z5,z6]),(0,[z0,z104,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z1011,z6]),(0,[z0,z1,z2,z4,z5,z1012]),(0,[z1013,z1,z2,z4,z5,z6])],[(0,[z29,z1,z2,z4,z5,z487]),(0,[z0,z1,z2,z4,z5,z1014]),(0,[z0,z1,z1015,z4,z5,z6]),(0,[z0,z477,z2,z4,z5,z30]),(0,[z140,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z5,z883,z8])]],
   [[(0,[z0,z1,z2,z4,z5,z1016]),(0,[z0,z1,z2,z4,z5,z1017]),(0,[z188,z1,z2,z176,z5,z6])],[(0,[z0,z1,z2,z4,z1018,z6]),(0,[z0,z1,z2,z4,z5,z1019]),(0,[z0,z1,z2,z4,z5,z1020]),(0,[z0,z1,z2,z4,z5,z1021]),(0,[z0,z1,z2,z1022,z5,z6]),(0,[z0,z1,z219,z45,z5,z8]),(0,[z0,z2,z4,z1023,z5,z6]),(0,[z0,z1,z2,z4,z307,z6]),(0,[z0,z1,z2,z57,z5,z24])],[(0,[z89,z2,z4,z5,z6,z269]),(0,[z1,z2,z4,z5,z849,z41]),(0,[z0,z257,z219,z4,z5,z6]),(0,[z86,z1,z2,z4,z5,z261]),(0,[z0,z1,z45,z5,z684,z8])],[(0,[z0,z1,z2,z510,z5,z8]),(0,[z0,z1,z2,z4,z5,z1024]),(0,[z0,z1,z2,z4,z5,z1025])],[(0,[z114,z1,z14,z4,z5,z24]),(0,[z12,z1,z2,z4,z5,z41])],[(0,[z0,z104,z2,z4,z5,z6]),(0,[z661,z43,z2,z4,z5,z6]),(0,[z140,z1,z2,z4,z5,z403]),(0,[z1,z386,z2,z135,z4,z5]),(0,[z0,z1,z2,z1026,z5,z6]),(0,[z0,z1,z2,z135,z4,z76])],[(0,[z0,z1,z2,z4,z5,z1027]),(0,[z40,z718,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z5,z128]),(0,[z0,z1,z2,z4,z545,z319])],[(0,[z0,z1028,z2,z4,z5,z6]),(0,[z0,z139,z2,z4,z297,z6]),(0,[z0,z1,z2,z4,z1029,z6]),(0,[z0,z1030,z2,z4,z5,z6]),(0,[z0,z1,z2,z71,z5,z883])]],
   [[(0,[z0,z1,z2,z1031,z4,z6]),(0,[z98,z2,z4,z61,z5,z6]),(0,[z0,z1,z2,z4,z5,z1032]),(0,[z0,z1,z2,z354,z5,z6]),(0,[z0,z1,z71,z427,z20,z6])],[(0,[z0,z1,z2,z4,z5,z565]),(0,[z0,z1033,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1034]),(0,[z93,z1,z2,z4,z28,z24]),(0,[z0,z1,z2,z4,z5,z746]),(0,[z1035,z0,z1,z2,z4,z5]),(0,[z0,z898,z2,z4,z5,z6]),(0,[z1,z1036,z2,z4,z5,z8])],[(0,[z0,z1,z2,z4,z1037,z6]),(0,[z0,z1,z338,z61,z5,z6])],[(0,[z43,z718,z2,z4,z5,z6]),(0,[z0,z1038,z2,z4,z5,z6]),(0,[z0,z1,z146,z45,z5,z6]),(0,[z0,z1,z2,z4,z5,z1039]),(0,[z0,z1,z2,z4,z5,z1040]),(0,[z0,z1,z2,z423,z5,z24])],[(0,[z0,z1,z2,z182,z5,z24]),(0,[z0,z1,z2,z481,z113,z6]),(0,[z1041,z1,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z1042,z6]),(0,[z0,z1,z1043,z4,z5,z6]),(0,[z0,z1,z2,z4,z1044,z6]),(0,[z1045,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z4,z811,z6])]],
   [[(0,[z188,z1,z2,z530,z5,z6]),(0,[z908,z1,z2,z4,z5,z6])],[(0,[z44,z43,z2,z4,z5,z6]),(0,[z0,z1046,z2,z4,z5,z6]),(0,[z0,z1,z427,z4,z5,z6]),(0,[z9,z0,z1,z132,z5,z8]),(0,[z196,z0,z1,z71,z20,z6]),(0,[z0,z1,z1047,z2,z4,z5]),(0,[z1,z1036,z2,z4,z5,z6])],[(0,[z140,z1,z2,z4,z5,z261]),(0,[z0,z1048,z2,z4,z5,z6]),(0,[z196,z0,z1,z4,z5,z359])],[(0,[z0,z1,z2,z4,z5,z760]),(0,[z0,z1,z2,z5,z75,z8]),(0,[z0,z1,z2,z135,z354,z5])],[(0,[z0,z1,z2,z440,z5,z8]),(0,[z0,z1,z2,z4,z1049,z5])],[(0,[z0,z1,z2,z4,z1050,z6])],[(0,[z0,z1,z2,z4,z5,z1051]),(0,[z0,z1,z2,z4,z5,z1052])],[(0,[z0,z1,z2,z4,z5,z1053]),(0,[z0,z1054,z2,z4,z5,z6]),(0,[z566,z0,z1,z4,z5,z125]),(0,[z64,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z1055,z5,z6]),(0,[z16,z0,z2,z1023,z5,z6]),(0,[z0,z1,z2,z53,z113,z8]),(0,[z42,z0,z2,z4,z5,z746])]],
   [[(0,[z89,z2,z4,z357,z5,z6]),(0,[z0,z1056,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1057,z5]),(0,[z1,z386,z2,z4,z56,z5])],[(0,[z0,z1,z2,z4,z5,z8]),(0,[z0,z129,z2,z4,z5,z8]),(0,[z7,z0,z1,z4,z255,z6])],[(0,[z0,z1,z2,z4,z5,z1058]),(0,[z0,z1,z2,z4,z5,z1059]),(0,[z663,z1,z2,z176,z5,z6]),(0,[z0,z571,z2,z4,z5,z90]),(0,[z0,z1,z2,z71,z20,z24])],[(0,[z0,z1,z2,z4,z1060,z6]),(0,[z0,z1,z2,z4,z1061,z6]),(0,[z29,z477,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z113,z84])],[(0,[z0,z1,z2,z1062,z4,z5]),(0,[z140,z1,z2,z4,z272,z6]),(0,[z0,z1,z2,z290,z5,z8])],[(0,[z460,z0,z2,z4,z5,z6]),(0,[z0,z1,z1063,z4,z5,z6]),(0,[z0,z1,z649,z45,z5,z6]),(0,[z0,z139,z2,z4,z153,z6]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z9,z0,z1,z691,z5,z6]),(0,[z0,z70,z2,z347,z4,z5]),(0,[z0,z1,z796,z45,z5,z6])],[(0,[z295,z0,z10,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1065]),(0,[z0,z1,z2,z241,z5,z24]),(0,[z0,z1,z2,z4,z5,z1066])],[(0,[z1,z715,z14,z4,z5,z6]),(0,[z0,z1,z2,z4,z1067,z6]),(0,[z27,z1,z2,z4,z92,z24]),(0,[z460,z0,z2,z4,z5,z621]),(0,[z1068,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1069,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1070,z5,z6]),(0,[z0,z1,z2,z4,z1071,z6]),(1,[z1,z2,z4,z712,z6]),(0,[z0,z1,z10,z45,z5,z8]),(0,[z0,z1,z2,z23,z113,z108])],[(0,[z0,z1,z14,z45,z5,z8]),(0,[z0,z1,z2,z4,z5,z1072]),(0,[z0,z1,z2,z579,z5,z8]),(0,[z0,z1,z2,z1073,z4,z8])],[(0,[z718,z80,z2,z4,z5,z6]),(0,[z0,z1,z338,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z1074]),(0,[z0,z477,z2,z4,z5,z8]),(0,[z0,z1,z463,z4,z5,z67]),(0,[z0,z1,z2,z57,z5,z41])],[(0,[z380,z0,z2,z145,z5,z6]),(0,[z0,z1,z2,z4,z5,z1075]),(0,[z0,z1,z2,z4,z5,z1076]),(0,[z0,z1,z2,z4,z256,z24]),(0,[z0,z1,z2,z4,z5,z1077]),(0,[z0,z1,z1078,z4,z5,z6]),(0,[z0,z1,z2,z4,z136,z24]),(0,[z1,z893,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1079]),(1,[z0,z1,z427,z5,z8]),(0,[z0,z1,z2,z20,z785,z6])],[(0,[z0,z1,z2,z4,z1080,z6]),(0,[z0,z1,z2,z4,z5,z1081]),(1,[z0,z1,z2,z732,z5]),(0,[z0,z1,z2,z113,z319,z8])],[(0,[z0,z1,z2,z4,z1082,z6]),(0,[z0,z1,z2,z4,z1083,z5]),(0,[z0,z1,z2,z4,z264,z24]),(0,[z0,z1,z2,z5,z361,z8]),(0,[z0,z1,z88,z4,z5,z537])],[(0,[z80,z89,z2,z4,z5,z269]),(0,[z292,z89,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1084,z6]),(0,[z293,z1,z2,z4,z28,z6]),(0,[z0,z1,z2,z4,z1085,z5]),(0,[z7,z0,z1,z2,z113,z8]),(0,[z0,z1,z2,z354,z56,z5]),(1,[z0,z1,z2,z785,z6])],[(0,[z0,z2,z1023,z145,z5,z6]),(0,[z0,z1,z2,z4,z5,z1086]),(0,[z1087,z1,z2,z4,z5,z6]),(0,[z0,z1,z117,z45,z5,z6])]],
   [[(0,[z43,z0,z2,z4,z5,z269]),(0,[z0,z1088,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1089]),(0,[z0,z1,z2,z1073,z4,z6]),(0,[z0,z1,z2,z4,z200,z24]),(0,[z0,z1,z2,z1090,z5,z6]),(0,[z0,z1,z2,z37,z5,z8]),(0,[z0,z1,z117,z4,z5,z167])],[(0,[z0,z1,z2,z4,z5,z1091]),(0,[z0,z477,z2,z4,z5,z6]),(0,[z0,z1,z2,z182,z5,z8]),(0,[z0,z1,z2,z4,z136,z403]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z0,z1,z2,z157,z5,z8])],[(0,[z0,z321,z2,z4,z5,z155]),(0,[z1092,z1,z2,z4,z5,z6]),(0,[z16,z140,z2,z145,z5,z6]),(0,[z0,z1,z2,z102,z5,z717])],[(1,[z89,z2,z4,z5,z269]),(0,[z0,z139,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z1093]),(0,[z0,z1,z2,z4,z5,z1094]),(0,[z0,z1,z2,z1023,z5,z6]),(0,[z0,z2,z4,z5,z121,z746]),(0,[z0,z1,z2,z4,z5,z1095]),(0,[z0,z1,z2,z1096,z5,z6])],[(0,[z333,z89,z2,z4,z5,z6]),(0,[z332,z0,z2,z4,z5,z121]),(0,[z0,z1,z1097,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1098]),(0,[z0,z1,z249,z2,z5,z24])],[(0,[z120,z0,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z272,z24]),(0,[z1099,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z234,z113,z6]),(0,[z0,z1,z2,z71,z785,z6])],[(0,[z0,z104,z2,z4,z5,z34]),(0,[z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z427,z4,z5,z359])]],
   [[(0,[z349,z89,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z297,z24]),(1,[z477,z2,z4,z5,z41]),(0,[z1100,z1,z2,z4,z5,z6]),(0,[z86,z1,z87,z4,z5,z6]),(0,[z0,z1,z2,z4,z200,z156])],[(0,[z718,z0,z2,z4,z5,z6]),(0,[z0,z1101,z2,z4,z5,z6]),(0,[z93,z321,z2,z4,z28,z6]),(0,[z69,z1,z2,z4,z5,z24]),(1,[z0,z2,z4,z5,z746]),(0,[z174,z1,z2,z4,z5,z105])],[(0,[z0,z1,z2,z4,z5,z1102]),(0,[z0,z1,z2,z4,z307,z75]),(0,[z949,z1,z2,z4,z5,z24])],[(0,[z1103,z0,z2,z4,z5,z6]),(0,[z1,z2,z4,z28,z712,z6]),(0,[z0,z1,z2,z4,z1104,z6]),(0,[z0,z1,z2,z4,z1105,z5])],[(0,[z175,z1,z2,z61,z5,z8]),(0,[z0,z1,z416,z45,z5,z6]),(0,[z0,z1,z1106,z4,z5,z6]),(0,[z1107,z1,z2,z4,z5,z6]),(0,[z0,z1,z775,z4,z5,z6]),(0,[z0,z1,z2,z4,z272,z403]),(0,[z0,z1,z4,z811,z112,z6])],[(0,[z0,z1,z2,z1108,z5,z6]),(0,[z120,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z1109,z4,z6]),(0,[z0,z1,z2,z4,z5,z1110]),(0,[z0,z1,z2,z622,z5,z8])],[(0,[z1111,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1112,z6]),(0,[z72,z477,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z1113]),(0,[z0,z1,z2,z4,z136,z261]),(0,[z0,z1,z2,z4,z5,z1114]),(0,[z0,z1,z71,z427,z5,z8])],[(0,[z0,z1,z88,z4,z5,z67])]],
   [[(0,[z0,z1,z2,z1115,z5,z6]),(0,[z0,z1,z2,z4,z5,z1116]),(0,[z0,z1,z132,z45,z5,z8])],[(0,[z0,z1,z2,z4,z5,z1117]),(0,[z0,z98,z2,z4,z5,z218]),(0,[z0,z1,z2,z4,z5,z1118]),(0,[z0,z1,z1119,z4,z5,z6]),(0,[z0,z1,z2,z135,z4,z159]),(0,[z0,z1,z2,z354,z5,z67])],[(0,[z40,z43,z2,z4,z5,z6]),(1,[z386,z2,z4,z5,z90]),(0,[z0,z1,z95,z45,z5,z258])],[(0,[z0,z1,z2,z4,z5,z1120]),(0,[z0,z1,z2,z4,z5,z1121]),(0,[z175,z1,z2,z61,z5,z6]),(0,[z0,z1,z2,z4,z5,z1122]),(0,[z0,z1,z1123,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1124])],[(0,[z0,z1,z2,z4,z5,z1125])],[(0,[z0,z1126,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1127]),(0,[z0,z1,z127,z45,z5,z8]),(0,[z0,z1,z1128,z4,z5,z6]),(0,[z0,z1,z2,z636,z5,z8])],[(0,[z229,z89,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z113,z24])],[(0,[z1129,z0,z2,z4,z5,z6])]],
   [[(1,[z1,z2,z4,z5,z849]),(0,[z140,z1,z87,z4,z5,z6]),(0,[z0,z1,z2,z32,z5,z24]),(0,[z0,z1,z45,z131,z5,z8]),(0,[z0,z1,z88,z2,z57,z5]),(0,[z0,z1,z1130,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1131]),(0,[z0,z1,z338,z176,z5,z6]),(0,[z0,z1,z2,z5,z650,z8]),(0,[z0,z1,z2,z4,z272,z261]),(0,[z0,z1,z2,z4,z5,z1132]),(0,[z0,z1,z2,z4,z5,z742])],[(0,[z0,z1,z2,z4,z5,z1133]),(0,[z114,z1,z715,z4,z5,z6]),(0,[z0,z1,z2,z48,z20,z6])],[(0,[z0,z1,z2,z4,z5,z1134]),(0,[z0,z1,z2,z4,z1135,z6]),(1,[z1,z715,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z218]),(0,[z0,z1,z2,z4,z5,z1136]),(0,[z74,z0,z2,z4,z52,z53]),(1,[z0,z1,z2,z307,z8]),(0,[z0,z1,z2,z4,z5,z1137]),(0,[z364,z0,z1,z2,z5,z75])],[(0,[z15,z0,z10,z4,z5,z24]),(0,[z0,z1,z2,z1138,z5,z6]),(0,[z0,z1,z2,z4,z1139,z5]),(0,[z0,z1,z2,z4,z1140,z6]),(0,[z7,z0,z1,z4,z112,z24]),(0,[z0,z1,z2,z71,z20,z355])],[(0,[z0,z1,z2,z4,z153,z24]),(0,[z72,z1,z2,z4,z5,z849]),(0,[z1141,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1142]),(0,[z0,z1,z2,z4,z56,z319])],[(0,[z0,z1,z2,z4,z5,z1143]),(0,[z1,z2,z4,z5,z849,z6]),(0,[z0,z1,z2,z1144,z5,z6]),(0,[z15,z0,z775,z4,z5,z6]),(0,[z74,z0,z2,z4,z53,z24])]],
   [[(0,[z134,z1,z127,z4,z5,z24])],[(0,[z0,z1,z2,z4,z5,z1145]),(0,[z9,z0,z1,z132,z5,z75]),(0,[z0,z1146,z2,z4,z5,z8]),(0,[z0,z1,z2,z83,z135,z150])],[(0,[z0,z1,z2,z4,z5,z1147]),(0,[z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z5,z1148]),(0,[z0,z1149,z2,z4,z5,z6])],[(0,[z0,z1,z127,z182,z5,z6]),(0,[z0,z1,z2,z4,z5,z1150]),(0,[z196,z0,z1,z4,z5,z24]),(0,[z0,z1,z2,z4,z742,z150])],[(0,[z0,z1,z2,z4,z5,z1151]),(0,[z141,z0,z10,z4,z5,z6]),(0,[z0,z1,z2,z5,z285,z8])],[(0,[z0,z1,z338,z4,z5,z218]),(0,[z1152,z0,z1,z4,z5,z6])],[(0,[z86,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z1153])],[(0,[z114,z104,z14,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z1154,z5,z6]),(0,[z0,z1155,z2,z4,z5,z6]),(1,[z0,z2,z4,z736,z6]),(0,[z0,z1146,z2,z4,z5,z6])],[(0,[z0,z98,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z1156]),(0,[z0,z1,z2,z4,z5,z75]),(0,[z7,z0,z1,z33,z4,z112]),(0,[z0,z1,z2,z5,z537,z8])],[(0,[z1157,z0,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z811,z6])],[(0,[z80,z89,z2,z4,z5,z24]),(0,[z175,z1,z2,z723,z5,z6])],[(0,[z0,z1,z109,z4,z5,z8]),(0,[z0,z1,z2,z5,z700,z8]),(0,[z0,z1,z2,z4,z5,z84])],[(0,[z86,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z704,z5,z8]),(0,[z0,z1,z2,z4,z1158,z6])],[(0,[z0,z1,z2,z4,z5,z1159])],[(0,[z0,z1,z2,z648,z5,z8]),(0,[z0,z1,z2,z92,z113,z8]),(0,[z0,z1,z2,z4,z1160,z5])]],
   [[(0,[z0,z98,z2,z4,z5,z6]),(0,[z0,z104,z2,z182,z5,z6]),(0,[z206,z0,z2,z4,z5,z228])],[(0,[z0,z1,z4,z5,z1161,z6]),(0,[z0,z1,z2,z4,z5,z1162]),(0,[z0,z1,z2,z4,z5,z1163]),(0,[z0,z1,z2,z234,z4,z360])],[(0,[z0,z1,z2,z4,z5,z1164]),(0,[z0,z1,z2,z4,z52,z5])],[(0,[z0,z104,z2,z4,z5,z190]),(0,[z0,z1,z109,z4,z5,z6]),(0,[z0,z1165,z2,z4,z5,z6]),(0,[z0,z877,z2,z4,z5,z6]),(0,[z0,z1,z2,z1166,z5,z6]),(1,[z0,z775,z4,z5,z6]),(0,[z0,z1,z2,z563,z113,z6]),(0,[z0,z1,z2,z4,z56,z447]),(0,[z9,z0,z1,z132,z5,z6]),(0,[z0,z1,z132,z796,z5,z6]),(0,[z0,z1,z2,z83,z5,z8])],[(0,[z0,z1167,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1168]),(0,[z0,z1,z2,z179,z5,z8]),(0,[z1169,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z71,z113,z8])],[(0,[z0,z1,z2,z36,z5,z8]),(0,[z0,z1,z2,z4,z5,z399]),(0,[z0,z1,z2,z5,z24,z577]),(0,[z0,z1,z2,z4,z5,z1170])],[(0,[z0,z1,z2,z4,z5,z1171]),(0,[z140,z1,z2,z4,z5,z8]),(0,[z206,z0,z2,z4,z5,z121]),(0,[z0,z1,z2,z354,z5,z361])],[(0,[z0,z512,z2,z4,z137,z6]),(0,[z0,z1,z1172,z4,z5,z6]),(0,[z175,z1,z2,z61,z5,z218]),(0,[z477,z2,z4,z5,z6,z41]),(0,[z232,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z354,z5,z24])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 527).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1053).take 161) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1214)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [527, 526, 161] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 99).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 208).take 48).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [99, 109, 48] = true :=
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

end PEqualNP.Outside.L_meta_46192

theorem PEqualNP.Outside.L_meta_46192 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46192.solve