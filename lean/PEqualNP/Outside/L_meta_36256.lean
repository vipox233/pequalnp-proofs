import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36256

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276681440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x11000200a045858a#64 ++ 0x022000401408b0b1#64 ++ 0xfec14633e0cf8f9f#64 ++ 0xbfd828c67c19f1f3#64 : BitVec 256),
   (0x0a0219258312cca4#64 ++ 0x21404324b0625994#64 ++ 0xbda6b92d8733cce7#64 ++ 0x77b4d725b0e6799c#64 : BitVec 256),
   (0xa408c04a08281050#64 ++ 0x948118094105020a#64 ++ 0xebd8c1ce183c70fe#64 ++ 0xfd7b1839c3078e1f#64 : BitVec 256),
   (0x081701b015806a00#64 ++ 0x2102e03602b00d40#64 ++ 0x67ff01f01fc07f05#64 ++ 0xecffe03e03f80fe0#64 : BitVec 256),
   (0x303dee001eff0000#64 ++ 0xc607bdc003dfe000#64 ++ 0x1fbffe001fff8003#64 ++ 0xe3f7ffc003fff000#64 : BitVec 256),
   (0xc01ff5ff40000000#64 ++ 0xf803febfe8000000#64 ++ 0xff9fffffe0000000#64 ++ 0x1ff3fffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [14, 13]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0015009014802200 0x0002a01202900440 0x425900d018c03300 0x884b201a03180660

def z1 : W := mkw 0x0a1719b59792eea4 0x2142e336b2f25dd4 0xffffb9fd9ff3ffe7 0xfffff73fb3fe7ffc

def z2 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec14633e0cf8f9f 0xbfd828c67c19f1f3

def z3 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z4 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd8c1ce183c70fe 0xfd7b1839c3078e1f

def z5 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffffc07f05 0xfffffffffff80fe0

def z6 : W := mkw 0x0000000080008480 0x0000000010001090 0xbc80002180038c87 0x3790000430007190

def z7 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z8 : W := mkw 0x1b021b25a357cdae 0x23604364b46af9b5 0xffe7ff3fe7ffcfff 0xfffcffe7fcfff9ff

def z9 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff83c70fe 0xfffbffffff078e1f

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0x66c1003000c00f05 0xacd82006001801e0

def z11 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe7b93d87f3cfe7 0xfffcf727b0fe79fc

def z12 : W := mkw 0x191703b0b5c5ef8a 0x2322e07616b8bdf1 0xffff47f3ffcfff9f 0xffffe8fe7ff9fff3

def z13 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z14 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff81fc1ff07f65 0xecfff03f83fe0fec

def z15 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda6b92d8733cce7 0x77b4d725b0e6799c

def z16 : W := mkw 0x0000080002120000 0x0000010000424000 0x1da6b80007338003 0x63b4d70000e67000

def z17 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xe31fffffe0000000 0x1c63fffffc000000

def z18 : W := mkw 0x303dee000a7f0000 0xc607bdc0014fe000 0x1fbffe00073f8003 0x63f7ffc000e7f000

def z19 : W := mkw 0x0000080002120000 0x0000010000424000 0x9da6b80c073380e3 0x73b4d70180e6701c

def z20 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x1fbffe0007cf8003 0xa3f7ffc000f9f000

def z21 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x77ff3ff1ffc07f05 0xeeffe7fe3ff80fe0

def z22 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x421946d260000000 0x084328da4c000000

def z23 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x153fbe001ff38001 0x42a7f7c003fe7000

def z24 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x151fbffde0000000 0x02a3f7ffbc000000

def z25 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xffffb9fd9ff07fe7 0xfffff73fb3fe0ffc

def z26 : W := mkw 0x2008c8000a3a0000 0x8401190001474000 0x1da6f800073f8003 0x63b4df0000e7f000

def z27 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x14273e0007c38001 0x0284e7c000f87000

def z28 : W := mkw 0x4000340540000000 0x48000680a8000000 0x10003e01e0000000 0x020007c03c000000

def z29 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x5fbffe127fff8003 0xebf7ffc24ffff000

def z30 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x013eb8001ff38001 0x4027d70003fe7000

def z31 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x67f901f01fc07f05 0xecff203e03f80fe0

def z32 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x14073e31e0000000 0x0280e7c63c000000

def z33 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x991effcfe0000000 0x1323dff9fc000000

def z34 : W := mkw 0xae0ad16f8928dcf4 0xb5c15a2df1251b9e 0xebd8c1ef983c7cfe 0xfd7b183df3078f9f

def z35 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9800fe0fe0000000 0x13001fc1fc000000

def z36 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffc1c633e0ff8f9f 0xfff838c67c1ff1f3

def z37 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xefff41f21fcc7f9f 0xfdffe83e43f98ff3

def z38 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x1000be0de0000000 0x020017c1bc000000

def z39 : W := mkw 0x4015249054802200 0x4802a4920a900440 0x425906d078c03300 0x884b20da0f180660

def z40 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xfe81fe3fe0000000 0x1fd03fc7fc000000

def z41 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0xffd9c7fff8ffffff 0xfffb38ffff1fffff

def z42 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0xfffffffffffc7fff 0xffffffffffff8fff

def z43 : W := mkw 0x0015080016920000 0x0002a10002d24000 0x17bf38001fc38001 0xe2f7e70003f87000

def z44 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe6f92f873fccff 0xfffcdf25f0e7f99f

def z45 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xe2414633e0cf8f9f 0xbc4828c67c19f1f3

def z46 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b90c0733c0e7 0x77b4d72180e6781c

def z47 : W := mkw 0xb428ee4a0a7f1050 0xd6851dc9414fe20a 0x9800fe0e003f80fa 0x13001fc1c007f01f

def z48 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa000012d80004ce4 0x14000025b000099c

def z49 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x0427003007c00f01 0x0084e00600f801e0

def z50 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x8800c00e003c00fa 0x11001801c007801f

def z51 : W := mkw 0x10200a0016d70000 0x0204014002dae000 0x1da6b80007f38003 0x63b4d70000fe7000

def z52 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9fffffe03c00fa 0x1ff3fffffc07801f

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0xa980810c003040e6 0x753010218006081c

def z54 : W := mkw 0x0000080002120000 0x0000010000424000 0x1426380007038001 0x0284c70000e07000

def z55 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff80c3018 0x9ffbffffff018603

def z56 : W := mkw 0xc81ff5ff41006a00 0xf903febfe8200d40 0xff9fffffe0000f00 0x1ff3fffffc0001e0

def z57 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xe2414633e0cc0f9c 0x9c4828c67c1981f3

def z58 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x013eb8001f300000 0x4027d70003e60000

def z59 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xefff81fc1ff07fe7 0xfdfff03f83fe0ffc

def z60 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x10007e03e0000000 0x02000fc07c000000

def z61 : W := mkw 0xb53dee4abeff95da 0xd6a7bdc957dff2bb 0xffffffffffffffff 0xffffffffffffffff

def z62 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xe04001ed80007ce4 0x1c08003db0000f9c

def z63 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xfffeb9ed9f33fce7 0xffffd73db3e67f9c

def z64 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x1507bf3de0000000 0x02a0f7e7bc000000

def z65 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0x0060000007cf8f9f 0xa00c000000f9f1f3

def z66 : W := mkw 0x303dee901eff2200 0xc607bdd203dfe440 0x5ffffed01fffb303 0xebffffda03fff660

def z67 : W := mkw 0x081709b017926a00 0x2102e13602f24d40 0x7fffb9f01ff3ff07 0xeffff73e03fe7fe0

def z68 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67bf01f007c00f01 0x0cf7e03e00f801e0

def z69 : W := mkw 0x1a373f2597d7cca4 0x6346e7e4b2faf994 0xbda7bf2d87f3cce7 0x77b4f7e5b0fe799c

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814633e0000000 0x1fd028c67c000000

def z71 : W := mkw 0xd11ff7ffe045858a 0xfa23fefffc08b0b1 0xffdfffffe0cf8f9f 0xbffbfffffc19f1f3

def z72 : W := mkw 0xe41df44f48281050 0xdc83be89e905020a 0x9f9ffe0ff83c00fa 0xf3f3ffc1ff07801f

def z73 : W := mkw 0x0a1719b59792eea4 0x2142e336b2f25dd4 0xbda7b93d87f3cfe7 0x77b4f727b0fe79fc

def z74 : W := mkw 0xac1fc1fa1da87a50 0xb583f83f43b50f4a 0x8c27c03e07fc0ffb 0x1184f807c0ff81ff

def z75 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0x77ff39f19fc07f05 0xeeffe73e33f80fe0

def z76 : W := mkw 0x0002112500000000 0x20004224a0000000 0xbd86b92d80000000 0x17b0d725b0000000

def z77 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xffffffce1ffff0ff 0xfffffff9c3fffe1f

def z78 : W := mkw 0xca1ffdffc312cca4 0xf943ffbff8625994 0xffbfffffe733cce7 0x7ff7fffffce6799c

def z79 : W := mkw 0xf03fffff5eff0000 0xfe07ffffebdfe000 0xffbfffffffff8003 0xfff7fffffffff000

def z80 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xa9d881cc183c70fe 0xf53b103983078e1f

def z81 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0xe040013fe0004ffc 0x1c080027fc0009ff

def z82 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x001800c018003000 0x0003001803000600

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0xebc0c10e003c40fe 0xfd781821c007881f

def z84 : W := mkw 0xae0ad96f8b3adcf4 0xb5c15b2df1675b9e 0xfffef9ef9f3ffcff 0xffffdf3df3e7ff9f

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401003000c00f01 0x00802006001801e0

def z86 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x0126b90c07304060 0x4024d72180e6080c

def z87 : W := mkw 0x11000a00a257858a 0x02200140144af0b1 0xffe7fe33e7ff8f9f 0xfffcffc67cfff1f3

def z88 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x5ffffec21fffb01b 0xebffffd843fff603

def z89 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xb926b92d8733cce6 0x5724d725b0e6799c

def z90 : W := mkw 0x001701b000000000 0x2002e03600000000 0x679f01f000000000 0x0cf3e03e00000000

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x63d801c018007004 0xec7b003803000e00

def z92 : W := mkw 0xac1fc1fa1da87a50 0xb583f83f43b50f4a 0xefffc1fe1ffc7fff 0xfdfff83fc3ff8fff

def z93 : W := mkw 0x081701b001006a00 0x2102e03600200d40 0x67df01f000007f04 0x0cfbe03e00000fe0

def z94 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1426382187038c01 0x0284c70430e07180

def z95 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x425840c2180c3018 0x884b081843018603

def z96 : W := mkw 0x8400004a00001050 0x108000094000020a 0xe04001ce000070fc 0x1c080039c0000e1f

def z97 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x9c014633e0cf8f9b 0x138028c67c19f1f3

def z98 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x637f01f01fc07f04 0xcc6fe03e03f80fe0

def z99 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xde414633e0cf8f9b 0x9bc828c67c19f1f3

def z100 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xbfbfff0c1fffc0e7 0xf7f7ffe183fff81c

def z101 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x561f7ef3e0000000 0x0ac3efde7c000000

def z102 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x14273e0007f38003 0x6284e7c000fe7000

def z103 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdffffff8007004 0xfffbffffff000e00

def z104 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdffffff8003000 0x9ffbffffff000600

def z105 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe03000e2 0x1ff3fffffc06001c

def z106 : W := mkw 0x1a373f2597d7cca4 0x6346e7e4b2faf994 0x14273e2187c38c01 0x0284e7c430f87180

def z107 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xf51fbfffe0000000 0x1ea3f7fffc000000

def z108 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xe040013d80004fe4 0x1c080027b00009fc

def z109 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x8000002d80000ce0 0x10000005b000019c

def z110 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9c26b82d87338ce3 0x1384d705b0e6719c

def z111 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe25841ce183c70fe 0xfc4b0839c3078e1f

def z112 : W := mkw 0x30200a001eff0000 0x0604014003dfe000 0x1fa7fe001fff8003 0xe3f4ffc003fff000

def z113 : W := mkw 0x0815009015806a00 0x0102a01202b00d40 0x427900d01fc07f05 0xe84f201a03f80fe0

def z114 : W := mkw 0xb43de64a1ced1050 0xd687bcc9439da20a 0x425946c218cc3018 0x884b28d843198603

def z115 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x111ebfcde0000000 0x0223d7f9bc000000

def z116 : W := mkw 0xca1decdac312cca4 0xd943bd9b58625994 0x423946d26733cce7 0x684728da4ce6799c

def z117 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe000009c 0x1ffbfffffc000013

def z118 : W := mkw 0x30200a001eff0000 0x0604014003dfe000 0x002000001fff8003 0xe004000003fff000

def z119 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe03040e6 0x7ff3fffffc06081c

def z120 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xfe877e33e0000000 0x1fd0efc67c000000

def z121 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x015881cc183c70fe 0xe02b103983078e1f

def z122 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1ea77e0007cf8003 0xa3d4efc000f9f000

def z123 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x163f7e001fcf8001 0x82c7efc003f9f000

def z124 : W := mkw 0x001701b000000000 0x2002e03600000000 0x67df01f000c00f05 0xacfbe03e001801e0

def z125 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xefffc1fe1ffc7fff 0xfdfff83fc3ff8fff

def z126 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0x1ffffe001fff831b 0xe3ffffc003fff063

def z127 : W := mkw 0xb43de64a1ced1050 0xd687bcc9439da20a 0xebd9c7ce18fc70fe 0xfd7b38f9c31f8e1f

def z128 : W := mkw 0xa41dec4a0a3a1050 0xd483bd894147420a 0xffffffce1f3ff0ff 0xfffffff9c3e7fe1f

def z129 : W := mkw 0x0015000014800000 0x0002a00002900000 0x07bf00001fc00001 0xe0f7e00003f80000

def z130 : W := mkw 0x382aefb00b7f6a00 0xe7055df6016fed40 0x7840fff0003fff06 0x0f081ffe0007ffe0

def z131 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x14273e001fff8003 0xe284e7c003fff000

def z132 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe25841ce180c70fc 0x9c4b0839c3018e1f

def z133 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x63f801c01fc07f05 0xec7f003803f80fe0

def z134 : W := mkw 0x0000080002120000 0x0000010000424000 0x0126b80007338003 0x6024d70000e67000

def z135 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1526b92d8733cc61 0x42a4d725b0e6798c

def z136 : W := mkw 0x201dec000a3a0000 0xc403bd8001474000 0x1fbffe001f3f8003 0xe3f7ffc003e7f000

def z137 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x013e01c01f007000 0x4027c03803e00e00

def z138 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x98004603e00f809a 0x130008c07c01f013

def z139 : W := mkw 0x02001805821284a4 0x00400300b0425094 0x9da6b80d873380e3 0x73b4d701b0e6701c

def z140 : W := mkw 0x080201b001006a00 0x2100403600200d40 0x63d801f018007f04 0xec7b003e03000fe0

def z141 : W := mkw 0x3028ee000a7f0000 0xc6051dc0014fe000 0x1800fe00003f8002 0x03001fc00007f000

def z142 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x1fbfb8001ff38003 0xe3f7f70003fe7000

def z143 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x8918c1ce183c70fa 0x51231839c3078e1f

def z144 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xfde6b93d8733cfe7 0x7fbcd727b0e679fc

def z145 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xefd9c1fe183c70fe 0xfdfb383fc3078e1f

def z146 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x3da6b92c0733cc67 0x67b4d72580e6798c

def z147 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x625901f018c07f04 0x8c4b203e03180fe0

def z148 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x0000002180000c00 0x0000000430000180

def z149 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffd947f3f8cfff9f 0xfffb28fe7f19fff3

def z150 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9926b90d8733c0e2 0x5324d721b0e6781c

def z151 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe0c00f05 0xbffbfffffc1801e0

def z152 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9ffffff83c70fa 0x5ff3ffffff078e1f

def z153 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x63d881cc183c70fe 0xec7b103983078e1f

def z154 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x033ffe001fff8003 0xe067ffc003fff000

def z155 : W := mkw 0x383fefb01fff6a00 0xe707fdf603ffed40 0x7ffffff01fffff07 0xeffffffe03ffffe0

def z156 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x14273e31e7c00f01 0x0284e7c63cf801e0

def z157 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xffdffffff83c009e 0xfffbffffff078013

def z158 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x0000010c00004ce4 0x000000218000099c

def z159 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x1da6b90c0733c063 0x63b4d72180e6780c

def z160 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x011eb9cc00000000 0x0023d73980000000

def z161 : W := mkw 0x02001805821284a4 0x00400300b0425094 0x9800b80d803380e2 0x13001701b006701c

def z162 : W := mkw 0x080201b001006a00 0x2100403600200d40 0x0000003000000f00 0x00000006000001e0

def z163 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xff9fbffde0000000 0x1ff3f7ffbc000000

def z164 : W := mkw 0x0015009000000000 0x0002a01200000000 0x421900d000000000 0x0843201a00000000

def z165 : W := mkw 0xca0ad1ffc100cca4 0xb9415a3ff8201994 0xeb98c1ffe0304ce6 0x7d73183ffc06099c

def z166 : W := mkw 0xca0211ffc100cca4 0x3940423ff8201994 0xe00001ffe0004ce4 0x1c00003ffc00099c

def z167 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xfffffe33ffff809f 0xffffffc67ffff013

def z168 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x011881cc18307060 0x4023103983060e0c

def z169 : W := mkw 0x10202e0002570000 0x420405c0004ae000 0x10003e0000038000 0x020007c000007000

def z170 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0x7f9ffff1e0000000 0x0ff3fffe3c000000

def z171 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x76c10631e0c38f05 0xaed820c63c1871e0

def z172 : W := mkw 0x3a3fffb59fffeea4 0xe747fff6b3fffdd4 0xfffffffd9fffffe7 0xffffffffb3fffffc

def z173 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xfffffec21fffb09f 0xffffffd843fff613

def z174 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xbde6b92d8733cfff 0x77bcd725b0e679ff

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0xeac04002000c009e 0xbd58080040018013

def z176 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0x1fbffe001ffff063 0xe3f7ffc003fffe0c

def z177 : W := mkw 0x4a173db5c312cca4 0x6942e7b6b8625994 0xbda7bf3de733cce7 0x77b4f7e7bce6799c

def z178 : W := mkw 0x1000020000450000 0x020000400008a000 0xfec1460200cf809f 0xbfd828c04019f013

def z179 : W := mkw 0x0a0219b58312cca4 0x21404336b0625994 0xfda6b9fd8733cce7 0x7fb4d73fb0e6799c

def z180 : W := mkw 0x2008c00008280000 0x8401180001050000 0x0b98c000183c0002 0xe173180003078000

def z181 : W := mkw 0x801de44a00000000 0xd003bc8940000000 0xff9fffce00000000 0x1ff3fff9c0000000

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0xebd841c2180c709e 0xfd7b083843018e13

def z183 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffe7c00f01 0x1ff7fffffcf801e0

def z184 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x07bfb8001fff8003 0xe0f7f70003fff000

def z185 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x0126b90c0733cce7 0x6024d72180e6799c

def z186 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x017e01c01fc07f05 0xe02fc03803f80fe0

def z187 : W := mkw 0xc00211ff40000000 0x3800423fe8000000 0xe00001ffe0000000 0x1c00003ffc000000

def z188 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x77ff3fc01fc3f005 0xeeffe7f803f87e00

def z189 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xfb98ffcfe0000000 0x1f731ff9fc000000

def z190 : W := mkw 0x0000100500000000 0x00000200a0000000 0x9800b80d80000000 0x13001701b0000000

def z191 : W := mkw 0xca0afd6fc312cca4 0xf9415fadf8625994 0xbda6ff2fe733cce7 0x77b4dfe5fce6799c

def z192 : W := mkw 0x1000020000450000 0x020000400008a000 0x1e81460000cf8003 0xa3d028c00019f000

def z193 : W := mkw 0x313dee00beff858a 0xc627bdc017dff0b1 0xfffffe33ffff8f9f 0xffffffc67ffff1f3

def z194 : W := mkw 0x50373fb556d70000 0x6a06e7f6aadae000 0x14273e31e7c38001 0x0284e7c63cf87000

def z195 : W := mkw 0xca02116fc100cca4 0x3940422df8201994 0xa000012fe0004ce4 0x14000025fc00099c

def z196 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0x1f9ffe31e0000000 0x03f3ffc63c000000

def z197 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffe7c00f05 0xbffffffffcf801e0

def z198 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0xf4073fffe0000000 0x1e80e7fffc000000

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xbd86b90c00000000 0x17b0d72180000000

def z200 : W := mkw 0x0015240000000000 0x4002a48000000000 0xfe877e33e0000000 0x1fd0efc67c000000

def z201 : W := mkw 0xc01df44f40000000 0xd803be89e8000000 0x9a19fe0fe0000000 0x13433fc1fc000000

def z202 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd8c1fe183c7ffe 0xfd7b183fc3078fff

def z203 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x053f01f01fc07f01 0x40a7e03e03f80fe0

def z204 : W := mkw 0x0002112500000000 0x20004224a0000000 0xbd86ff2fe0000000 0x17b0dfe5fc000000

def z205 : W := mkw 0xc00af56f40000000 0xf8015eade8000000 0xbd86ff2fe0000000 0x17b0dfe5fc000000

def z206 : W := mkw 0x4a0211b5c100cca4 0x29404236b8201994 0x00000031e0000c00 0x000000063c000180

def z207 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x00004002000c0018 0x0000080040018003

def z208 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0x1ffffe001ffff0ff 0xe3ffffc003fffe1f

def z209 : W := mkw 0x1b021b252357492e 0x23604364a46ae925 0x4367ff1e67fc4378 0xc86cffe3ccff886f

def z210 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x14010631e0c38f01 0x028020c63c1871e0

def z211 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x67ff39f01fc07f05 0xecffe73e03f80fe0

def z212 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xff9ffffff83c0002 0xfff3ffffff078000

def z213 : W := mkw 0x001fe5b000000000 0xe003fcb600000000 0xff9ffff3e0000000 0x1ff3fffe7c000000

def z214 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0x151987fdf8f3ff61 0x42a330ffbf1e7fec

def z215 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffd9c7fff83c70fe 0xfffb38ffff078e1f

def z216 : W := mkw 0x0015080016920000 0x0002a10002d24000 0x1fbfb8001ff38003 0xe3f7f70003fe7000

def z217 : W := mkw 0x1b020b20a357cdae 0x23604164146af9b5 0x67e7013007ffcfff 0xecfce02600fff9ff

def z218 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0x9800fe0fe03c00fa 0x13001fc1fc07801f

def z219 : W := mkw 0x0802012001004800 0x2100402400200900 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z220 : W := mkw 0xa408c84a0a3a1050 0x948119094147420a 0x1dbeb9cc1f33f063 0x63b7d73983e67e0c

def z221 : W := mkw 0x2408c00008281050 0x848118000105020a 0x0bd8c000183c70fe 0xe17b180003078e1f

def z222 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xefd9c1fe18fc7fff 0xfdfb383fc31f8fff

def z223 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x17bf3e001fc38001 0xe2f7e7c003f87000

def z224 : W := mkw 0x0a1711b515806a24 0x2142e236a2b00d44 0x67ff01fc1fc07f65 0xecffe03f83f80fec

def z225 : W := mkw 0x0002112500000000 0x20004224a0000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z226 : W := mkw 0x0a0008008312cca4 0x0140010010625994 0x002000000733cce7 0x6004000000e6799c

def z227 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0xffffffffffcc7f1d 0xfffffffffff98fe3

def z228 : W := mkw 0x0a0219b58312eea4 0x21404336b0625dd4 0xffe7b9fd87f3ffe7 0xfffcf73fb0fe7ffc

def z229 : W := mkw 0x2400000008281050 0x048000000105020a 0xebd881cc183c70fe 0xfd7b103983078e1f

def z230 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff80c70fc 0x9ffbffffff018e1f

def z231 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0x9c07fe3fe03c00fa 0x1380ffc7fc07801f

def z232 : W := mkw 0x001dec0002120000 0xc003bd8000424000 0x1dbeb80007338003 0x63b7d70000e67000

def z233 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x013e01c01fc07f01 0x4027c03803f80fe0

def z234 : W := mkw 0x2400000008281050 0x048000000105020a 0x00400000183c70fe 0xe008000003078e1f

def z235 : W := mkw 0xc01df44f40000000 0xd803be89e8000000 0x9c07fe0fe0000000 0x1380ffc1fc000000

def z236 : W := mkw 0x0802012001004800 0x2100402400200900 0x0426002007000c01 0x0084c00400e00180

def z237 : W := mkw 0x021518959692a6a4 0x0042a312b2d254d4 0xda59b8dd98f3b3e2 0x9b4b371bb31e767c

def z238 : W := mkw 0xf03deeda5eff0000 0xde07bddb4bdfe000 0x5fbffed27fff8003 0xebf7ffda4ffff000

def z239 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x163f7e0007c38001 0x02c7efc000f87000

def z240 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd8c1ce18fc7fff 0xfd7b1839c31f8fff

def z241 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xfde6b93fe733cfff 0x7fbcd727fce679ff

def z242 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffff007f04 0x5fffffffffe00fe0

def z243 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xe7ff01f3ffc07f05 0xfcffe03e7ff80fe0

def z244 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x779f3ff1e0000000 0x0ef3e7fe3c000000

def z245 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0x565f7ef3f80c3018 0x8acbefde7f018603

def z246 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9ffffff8307060 0x5ff3ffffff060e0c

def z247 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0x9800fe0fe0300060 0x13001fc1fc06000c

def z248 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x9fbffe03ffff8003 0xf3f7ffc07ffff000

def z249 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x467f00f01fc03f01 0x88cfe01e03f807e0

def z250 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xbfbffe001fff8087 0xf7f7ffc003fff010

def z251 : W := mkw 0x0015240014800000 0x4002a48002900000 0x17bf3e001fc00001 0xe2f7e7c003f80000

def z252 : W := mkw 0x0802012001004800 0x2100402400200900 0x25a6012007004c05 0x64b4c02400e00980

def z253 : W := mkw 0xa408c04a882894d0 0x948118095105129a 0xffd8c1ef983ffcff 0xfffb183df307ff9f

def z254 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x425840c2183c70fe 0xe84b081843078e1f

def z255 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x1dbeb8001f338003 0x63b7d70003e67000

def z256 : W := mkw 0x080201b001006a00 0x2100403600200d40 0x604001f000007f04 0x0c08003e00000fe0

def z257 : W := mkw 0xf13deeda7eff010a 0xde27bddb4fdfe021 0x5ffffed27fff831b 0xebffffda4ffff063

def z258 : W := mkw 0xe41ff5ff5ca81050 0xfc83febfeb95020a 0xfffffffffffc70ff 0xffffffffffff8e1f

def z259 : W := mkw 0x0000000080008480 0x0000000010001090 0xfe814633e0038c87 0x3fd028c67c007190

def z260 : W := mkw 0xae0ad16f8928dcf4 0xb5c15a2df1251b9e 0xe25841ef980c7cfc 0x9c4b083df3018f9f

def z261 : W := mkw 0x0a0008008312cca4 0x0140010010625994 0xa9a0810c0733cce7 0x7534102180e6799c

def z262 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x9c07fe3fe0000000 0x1380ffc7fc000000

def z263 : W := mkw 0x10000a0002570000 0x02000140004ae000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z264 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xffffffffffc07f05 0xfffffffffff80fe0

def z265 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffffc03f01 0x9ffffffffff807e0

def z266 : W := mkw 0xc00af5ff40000000 0xf8015ebfe8000000 0xf800ffffe0000000 0x1f001ffffc000000

def z267 : W := mkw 0x3a3ff7259dedcca4 0xe747fee4b3bdb994 0xa219472d98cc4ce4 0x944328e5b319899c

def z268 : W := mkw 0x3a3fff259fffcca4 0xe747ffe4b3fff994 0xbfbfff2d9fffcce7 0xf7f7ffe5b3fff99c

def z269 : W := mkw 0x10200a0016d70000 0x0204014002dae000 0x0020000007c38001 0x0004000000f87000

def z270 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x25a6b92c0733cce7 0x64b4d72580e6799c

def z271 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xfe81473fe0004ce4 0x1fd028e7fc00099c

def z272 : W := mkw 0x313dee903eff230a 0xc627bdd207dfe461 0x5ffffed27fffb31b 0xebffffda4ffff663

def z273 : W := mkw 0xc81ff5ff41006a00 0xf903febfe8200d40 0xffdfffffe0007f04 0x1ffbfffffc000fe0

def z274 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x1f9ffe0000000000 0x03f3ffc000000000

def z275 : W := mkw 0x703fffb55eff0000 0xee07fff6abdfe000 0x1fbffe31ffff8003 0xe3f7ffc63ffff000

def z276 : W := mkw 0x94352e4a16d71050 0x5286a5c942dae20a 0xf4673fce07c3f0fd 0x1e8ce7f9c0f87e1f

def z277 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xea58c1ce183c70fe 0x9d4b1839c3078e1f

def z278 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x153fbfcc1ff3f061 0x42a7f7f983fe7e0c

def z279 : W := mkw 0x0000080002120000 0x0000010000424000 0x9800b80c003380e2 0x130017018006701c

def z280 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffdef9ce183c70fe 0xfffbdf39c3078e1f

def z281 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xffff47f3ffcc7f9f 0xffffe8fe7ff98ff3

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x011801c018007000 0x4023003803000e00

def z283 : W := mkw 0x3028ee000a7f0000 0xc6051dc0014fe000 0x1c26fe00073f8003 0x0384dfc000e7f000

def z284 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x1fbfffcc1ffff063 0xe3f7fff983fffe0c

def z285 : W := mkw 0xf43fffff5eff1050 0xfe87ffffebdfe20a 0xfffffffffffff0ff 0xfffffffffffffe1f

def z286 : W := mkw 0x081725b015806a00 0x6102e4b602b00d40 0x77ff3ff01fc07f05 0xeeffe7fe03f80fe0

def z287 : W := mkw 0xa43dec4a1eba1050 0xd487bd8943d7420a 0x013eb9cc1f307060 0x4027d73983e60e0c

def z288 : W := mkw 0x4000340540000000 0x48000680a8000000 0x14013e31e0000000 0x028027c63c000000

def z289 : W := mkw 0x091701b0b580ef8a 0x2122e03616b01df1 0xe7ff01f3ffc07f9d 0xfcffe03e7ff80ff3

def z290 : W := mkw 0x1b021325a145cdae 0x23604264b428b9b5 0xe241473fe0cc4ffc 0x9c4828e7fc1989ff

def z291 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x1f9ffffde0000000 0x03f3ffffbc000000

def z292 : W := mkw 0x0a0211b58100eea4 0x21404236b0201dd4 0xe04001fd80007fe4 0x1c08003fb0000ffc

def z293 : W := mkw 0x0a0219b58312eea4 0x21404336b0625dd4 0xfde6b9fd8733ffe7 0x7fbcd73fb0e67ffc

def z294 : W := mkw 0x2a3ffd251fba4824 0xe547ffa4a3f74904 0x013eb90c1f304060 0x4027d72183e6080c

def z295 : W := mkw 0x303de6001ced0000 0xc607bcc0039da000 0x0219460018cc0000 0x804328c003198000

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc80000000038087 0x3790000000007010

def z297 : W := mkw 0x8e02116f8100dcf4 0x31c0422df0201b9e 0xe04001ef80007cfc 0x1c08003df0000f9f

def z298 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x1fbffe0007f38003 0x63f7ffc000fe7000

def z299 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x35a6b92d8733cc65 0x66b4d725b0e6798c

def z300 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7fffffc01ffff007 0xeffffff803fffe00

def z301 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xda18fecfe0000000 0x1b431fd9fc000000

def z302 : W := mkw 0x00152c0002120000 0x4002a58000424000 0x1da7be0007338003 0x63b4f7c000e67000

def z303 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xb980ff0fe03040e6 0x77301fe1fc06081c

def z304 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xffff47f3ffc07f05 0xffffe8fe7ff80fe0

def z305 : W := mkw 0x31200a00beff858a 0x0624014017dff0b1 0x006000001fff8f9f 0xe00c000003fff1f3

def z306 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffbeb9ed8733cce7 0x7ff7d73db0e6799c

def z307 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x1da7be001fff8003 0xe3b4f7c003fff000

def z308 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffa7ff3fe733cce7 0x7ff4ffe7fce6799c

def z309 : W := mkw 0xf0221bff5eff0000 0x3e04437febdfe000 0xe02001ffffff8003 0xfc04003ffffff000

def z310 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbfbeb92d9f33cce7 0xf7f7d725b3e6799c

def z311 : W := mkw 0x001dec0002120000 0xc003bd8000424000 0x1fbffe0007038001 0x03f7ffc000e07000

def z312 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1826fe00073f8002 0x0304dfc000e7f000

def z313 : W := mkw 0x0000000000000000 0x0000000000000000 0x67d901f018c07f05 0xecfb203e03180fe0

def z314 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0xfbd8ffcff83c70fe 0xff7b1ff9ff078e1f

def z315 : W := mkw 0x0802012015806a00 0x2100402402b00d40 0x67fe01e01fc07f05 0xecffc03c03f80fe0

def z316 : W := mkw 0xc01ff5ff54800000 0xf803febfea900000 0xffffffffffc00f05 0xfffffffffff801e0

def z317 : W := mkw 0x213dec00beba858a 0xc427bd8017d750b1 0xe17eb833ff300f9c 0x5c2fd7067fe601f3

def z318 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe001ff38001 0x43f7ffc003fe7000

def z319 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b90c07338003 0x77b4d72180e67000

def z320 : W := mkw 0x0a0219259792eea4 0x21404324b2f25dd4 0xbde6b92d9ff3ffe7 0xf7bcd725b3fe7ffc

def z321 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x1fbffec01fffb003 0xe3f7ffd803fff600

def z322 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xfa19ffffe0000000 0x1f433ffffc000000

def z323 : W := mkw 0x481ff5b555806a00 0xe903feb6aab00d40 0x7ffffff1ffc07f05 0xeffffffe3ff80fe0

def z324 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x9c27fe3fe7c00f01 0x1384ffc7fcf801e0

def z325 : W := mkw 0x11000a00a257858a 0x02200140144af0b1 0x0060000007ff8f9f 0xe00c000000fff1f3

def z326 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffe7c04f05 0x7ff7fffffcf809e0

def z327 : W := mkw 0x0a0008008312cca4 0x0140010010625994 0xbda6b90c0733cce7 0x77b4d72180e6799c

def z328 : W := mkw 0x0a1719b517926a24 0x2142e336a2f24d44 0x013eb9cc1f307060 0x4027d73983e60e0c

def z329 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9d26b92d8733cce3 0x53a4d725b0e6799c

def z330 : W := mkw 0x2008c8000a3a0000 0x8401190001474000 0x1fbef8001f3f8003 0xe3f7df0003e7f000

def z331 : W := mkw 0xa408c84a0a3a1050 0x948119094147420a 0xfffef9ce1f3ff0ff 0xffffdf39c3e7fe1f

def z332 : W := mkw 0x0a1719b59792eea4 0x2142e336b2f25dd4 0xbdbeb9ed9f33fce7 0x77b7d73db3e67f9c

def z333 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe958c1ce183c70fe 0x5d2b1839c3078e1f

def z334 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe001f3f8002 0x43f7ffc003e7f000

def z335 : W := mkw 0xc01ffdff42120000 0xf803ffbfe8424000 0xffbfffffe7338003 0x7ff7fffffce67000

def z336 : W := mkw 0x641735b548281050 0x6c82e6b6a905020a 0x14473e31f83c70fe 0xe288e7c63f078e1f

def z337 : W := mkw 0x0802112501004800 0x21004224a0200900 0xbda6b92d87004c05 0x77b4d725b0e00980

def z338 : W := mkw 0x10352e9016d72200 0x4206a5d202dae440 0x14273e1007c38301 0x0284e7c200f87060

def z339 : W := mkw 0x3008ca000a7f0000 0x86011940014fe000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z340 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0xda19fedfe0000000 0x1b433fdbfc000000

def z341 : W := mkw 0xc01ff5ff54802200 0xf803febfea900440 0xffdffffff8c03300 0x9ffbffffff180660

def z342 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x1926b90c0733c062 0x4324d72180e6780c

def z343 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x013eb8001fff8003 0xe027d70003fff000

def z344 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0x14073ffde0000000 0x0280e7ffbc000000

def z345 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffc1c73fe0ffcfff 0xfff838e7fc1ff9ff

def z346 : W := mkw 0x30200a000a7f0000 0x06040140014fe000 0x1da6b800073f8003 0x63b4d70000e7f000

def z347 : W := mkw 0x00352c0016920000 0x4006a58002d24000 0x1426380007038001 0x0284c70000e07000

def z348 : W := mkw 0x18372fb017d76a00 0x6306e5f602faed40 0x14273e3007c38f01 0x0284e7c600f871e0

def z349 : W := mkw 0xb428ca4a1eff1050 0x9685194943dfe20a 0xebf8c1ce1ffff0ff 0xfd7f1839c3fffe1f

def z350 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1427be0007f38001 0x0284f7c000fe7000

def z351 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x9fbffe0e1fff80fb 0xf3f7ffc1c3fff01f

def z352 : W := mkw 0x080201b015806a00 0x2100403602b00d40 0x63f801f01fc07f05 0xec7f003e03f80fe0

def z353 : W := mkw 0x0802012001004800 0x2100402400200900 0x67e7013007c04f05 0xecfce02600f809e0

def z354 : W := mkw 0xf03deeda5eff0000 0xde07bddb4bdfe000 0xffbfffde7fff8003 0xfff7fffbcffff000

def z355 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x56414633e0cf8f19 0x8ac828c67c19f1e3

def z356 : W := mkw 0xc01ff5ff54800000 0xf803febfea900000 0xffffffffffc07005 0xfffffffffff80e00

def z357 : W := mkw 0xe40af56f48281050 0xfc815eade905020a 0xffdeffeff83c70fe 0xfffbdffdff078e1f

def z358 : W := mkw 0xac1fc1fa1da87a50 0xb583f83f43b50f4a 0x67ff41f21fcc7f1d 0xecffe83e43f98fe3

def z359 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1da6b82187338c03 0x63b4d70430e67180

def z360 : W := mkw 0xe41de4da48281050 0xdc83bc9b4905020a 0xebd9c7de783c70fe 0xfd7b38fbcf078e1f

def z361 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xeac0c00e003c00fe 0xbd581801c007801f

def z362 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xfec77e33e00c009e 0xbfd8efc67c018013

def z363 : W := mkw 0x10000a0002570000 0x02000140004ae000 0x1da6b80007ff8003 0xe3b4d70000fff000

def z364 : W := mkw 0x11000a00a257858a 0x02200140144af0b1 0xffe7ff3fe7ffcfff 0xfffcffe7fcfff9ff

def z365 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x163f3e001fc38001 0x82c7e7c003f87000

def z366 : W := mkw 0x481711b555806a00 0x2902e236aab00d40 0x67ff01f1ffc07f05 0xecffe03e3ff80fe0

def z367 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0000c05 0x3ff3fffffc000180

def z368 : W := mkw 0x0015009014802200 0x0002a01202900440 0x67ff00f01fc03f05 0xecffe01e03f807e0

def z369 : W := mkw 0xae0ad16f8928dcf4 0xb5c15a2df1251b9e 0xa11881ed98307ce4 0x5423103db3060f9c

def z370 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xfffffffffffff0ff 0xfffffffffffffe1f

def z371 : W := mkw 0xa41de44a08281050 0xd483bc894105020a 0xffdfffce183c70fe 0xfffbfff9c3078e1f

def z372 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7ffffe301fff8f07 0xefffffc603fff1e0

def z373 : W := mkw 0xc81ff5ff41006a00 0xf903febfe8200d40 0xffdffffff8007f04 0xfffbffffff000fe0

def z374 : W := mkw 0x0002112500000000 0x20004224a0000000 0xbd86b92d803040e6 0x77b0d725b006081c

def z375 : W := mkw 0x0a0219b58312eea4 0x21404336b0625dd4 0xbda6b93d8733cfe7 0x77b4d727b0e679fc

def z376 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1c27be0007f38003 0x0384f7c000fe7000

def z377 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xffdffffff80070fc 0xfffbffffff000e1f

def z378 : W := mkw 0xe41ff5ff5ca83250 0xfc83febfeb95064a 0xffdffffff8cc3318 0x9ffbffffff198663

def z379 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0x5ffffe127fff831b 0xebffffc24ffff063

def z380 : W := mkw 0x3028ca001eff0000 0x8605194003dfe000 0x1fbef8001fff8003 0xe3f7df0003fff000

def z381 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xfbd8c7cff83c70fe 0xff7b18f9ff078e1f

def z382 : W := mkw 0xc01de4da54802200 0xd803bc9b4a900440 0x425946d278c03300 0x884b28da4f180660

def z383 : W := mkw 0xc01df44f40000000 0xd803be89e8000000 0x9f9ffe0fe0000000 0x13f3ffc1fc000000

def z384 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xbd87bf3de0000000 0x17b0f7e7bc000000

def z385 : W := mkw 0x400211b540000000 0x28004236a8000000 0x00000031e0000000 0x000000063c000000

def z386 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1ffffe001ffff007 0xe3ffffc003fffe00

def z387 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x1c27fe0007c38001 0x0384ffc000f87000

def z388 : W := mkw 0x0002192502120000 0x20004324a0424000 0xbda6b92d8733c0e7 0x77b4d725b0e6781c

def z389 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xffbfffffe7004c05 0x7ff7fffffce00980

def z390 : W := mkw 0x001dec0002120000 0xc003bd8000424000 0x1fbffe0007338003 0x63f7ffc000e67000

def z391 : W := mkw 0x18372fb017d76a00 0x6306e5f602faed40 0x77ff3ff01fc3ff05 0xeeffe7fe03f87fe0

def z392 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x7fffb9f01fc07f05 0xeffff73e03f80fe0

def z393 : W := mkw 0xb43deeda1eff3250 0xd687bddb43dfe64a 0x5ffffed21fffb31b 0xebffffda43fff663

def z394 : W := mkw 0xb428ee4a0a7f1050 0xd6851dc9414fe20a 0xbda6ff0e073fc0ff 0x77b4dfe1c0e7f81f

def z395 : W := mkw 0x2008c00008280000 0x8401180001050000 0xab98c10c183c40e6 0xf57318218307881c

def z396 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xffbfffffe7000c01 0x1ff7fffffce00180

def z397 : W := mkw 0x080201b015806a00 0x2100403602b00d40 0x606001f01fc07f05 0xec0c003e03f80fe0

def z398 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xb980ff0fe0000000 0x17301fe1fc000000

def z399 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xff9ffffff8300000 0x5ff3ffffff060000

def z400 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xa980c10e003c40fe 0x75301821c007881f

def z401 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffff007000 0x5ff7ffffffe00e00

def z402 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x8b98c00e183c00fa 0xf1731801c307801f

def z403 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xfffffe321fff8f9f 0xffffffc643fff1f3

def z404 : W := mkw 0x080201b001006a00 0x2100403600200d40 0x65e601f007007f05 0x6cbcc03e00e00fe0

def z405 : W := mkw 0x01000000a000858a 0x00200000140010b1 0xe0400033e0000f9c 0x1c0800067c0001f3

def z406 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffe7000000 0x1ff7fffffce00000

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100810c00304060 0x402010218006080c

def z408 : W := mkw 0x30200a001eff0000 0x0604014003dfe000 0x0126b8001fff8003 0xe024d70003fff000

def z409 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff80c309e 0xbffbffffff018613

def z410 : W := mkw 0x11021325a045858a 0x22204264b408b0b1 0xffc7ff3fe0cf8f9f 0xbff8ffe7fc19f1f3

def z411 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x63d841c2180c701c 0xec7b083843018e03

def z412 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa980812d80304ce6 0x75301025b006099c

def z413 : W := mkw 0x1035260014c50000 0x4206a4c00298a000 0x0001060000c00000 0x000020c000180000

def z414 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe00c009a 0x1ff3fffffc018013

def z415 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x5ffffe021fff801b 0xebffffc043fff003

def z416 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x006000001fc07f05 0xe00c000003f80fe0

def z417 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa180012d80004ce4 0x74300025b000099c

def z418 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1da7be0007f38003 0x63b4f7c000fe7000

def z419 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0xffbfffce1fff8003 0xfff7fff9c3fff000

def z420 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x1fbffe0007c38001 0x03f7ffc000f87000

def z421 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff01f01fcc7f9f 0xecffe03e03f98ff3

def z422 : W := mkw 0x01000000a000858a 0x00200000140010b1 0xfcc00033e0038f9f 0x3f9800067c0071f3

def z423 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x0126b90c0733c0e2 0x4024d72180e6781c

def z424 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0xfffffe021ffff0ff 0xffffffc043fffe1f

def z425 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0c00f01 0x1ff3fffffc1801e0

def z426 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x25be01e01f007c05 0x64b7c03c03e00f80

def z427 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xffffffce1fffb01b 0xfffffff9c3fff603

def z428 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x10063e01e0000000 0x0200c7c03c000000

def z429 : W := mkw 0x0002192502120000 0x20004324a0424000 0xbda6b92d87338003 0x77b4d725b0e67000

def z430 : W := mkw 0xca0219ffc312cca4 0x3940433ff8625994 0xfda6b9ffe733cce7 0x7fb4d73ffce6799c

def z431 : W := mkw 0xca1ff5ff41004824 0xf943febfe8200904 0xff9fffffe0004060 0x1ff3fffffc00080c

def z432 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0xff9ffe33e0000000 0x1ff3ffc67c000000

def z433 : W := mkw 0x303dee901eff2200 0xc607bdd203dfe440 0x1fbffec01fffb003 0xe3f7ffd803fff600

def z434 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7fbffe301fff8003 0xeff7ffc603fff000

def z435 : W := mkw 0xa43dec4a1eba1050 0xd487bd8943d7420a 0xbdbeb9cc1f33f0e7 0x77b7d73983e67e1c

def z436 : W := mkw 0x3128ca00beff858a 0x8625194017dff0b1 0xebf8c0021fff8f9f 0xfd7f180043fff1f3

def z437 : W := mkw 0xc90211ffe100ef8a 0x3920423ffc201df1 0xe04001ffe0007f9c 0x1c08003ffc000ff3

def z438 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffffcc7f9f 0xfffffffffff98ff3

def z439 : W := mkw 0xc01ff5ff54800000 0xf803febfea900000 0xffbfffffffc00001 0xfff7fffffff80000

def z440 : W := mkw 0x30200a001eff0000 0x0604014003dfe000 0x1da6b8001fff8003 0xe3b4d70003fff000

def z441 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1126b90d8733c060 0x4224d721b0e6780c

def z442 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xa126b92d8733cce7 0x7424d725b0e6799c

def z443 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x0006380000000000 0x0000c70000000000

def z444 : W := mkw 0x591737b5f5c5ef8a 0x6b22e6f6beb8bdf1 0xffff7ff3ffcfff9f 0xffffeffe7ff9fff3

def z445 : W := mkw 0x0000080002120000 0x0000010000424000 0x1926b80007338002 0x4324d70000e67000

def z446 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe00c009e 0xbffbfffffc018013

def z447 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda6b92d8733cc61 0x57b4d725b0e6798c

def z448 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9da6b90d8733c0e3 0x73b4d721b0e6781c

def z449 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1ea7fe0007ff8003 0xa3d4ffc000fff000

def z450 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xeb98c1ce003c00fa 0x1d731839c007801f

def z451 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xbd87ff3fe0000000 0x17b0ffe7fc000000

def z452 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0xbfffff0c1ffff0ff 0xf7ffffe183fffe1f

def z453 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xfffffe021fff809f 0xffffffc043fff013

def z454 : W := mkw 0x303dee901eff0000 0xc607bdd203dfe000 0x5fbffed01fff8003 0xebf7ffda03fff000

def z455 : W := mkw 0x8a0ad16f8100cca4 0xb1415a2df0201994 0xeb98c1ef80004ce4 0x1d73183df000099c

def z456 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xf61f7fffe0000000 0x1ec3effffc000000

def z457 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xe7ff01fd9fc07f05 0xfcffe03fb3f80fe0

def z458 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9800fe0fe03000e2 0x13001fc1fc06001c

def z459 : W := mkw 0x801dec4a02120000 0xd003bd8940424000 0xffbfffce0733c0e7 0x7ff7fff9c0e6781c

def z460 : W := mkw 0xa408c84a0a3a1050 0x948119094147420a 0x9da6f80e073f80fb 0x73b4df01c0e7f01f

def z461 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x437f01d01fc07f05 0xe86fe03a03f80fe0

def z462 : W := mkw 0xb428ca4a1eff1050 0x9685194943dfe20a 0xfffef9ce1ffff0ff 0xffffdf39c3fffe1f

def z463 : W := mkw 0x2a0ad9258b3acca4 0xa5415b24b1675994 0xbfbef92d9f3fcce7 0xf7f7df25b3e7f99c

def z464 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x5f9ffed260000000 0x0bf3ffda4c000000

def z465 : W := mkw 0xa008c04a08280000 0x9401180941050000 0xeb98c1ce183c0002 0xfd731839c3078000

def z466 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x4358c1ce183c7078 0xc86b1839c3078e0f

def z467 : W := mkw 0xc81ff5ff41006a00 0xf903febfe8200d40 0xffffffffe7007f05 0x7ffffffffce00fe0

def z468 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xffbffe33ffff8003 0xfff7ffc67ffff000

def z469 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1c27fe001fff8003 0xe384ffc003fff000

def z470 : W := mkw 0x0815009015806a00 0x0102a01202b00d40 0x007800c01fc07f05 0xe00f001803f80fe0

def z471 : W := mkw 0x0a1711b59580eea4 0x2142e236b2b01dd4 0xe25901fd98c07fe4 0x9c4b203fb3180ffc

def z472 : W := mkw 0xe41df4df48281050 0xdc83be9be905020a 0xfbd9ffdff83c70fe 0xff7b3ffbff078e1f

def z473 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xa9a6b90c0733cce7 0x7534d72180e6799c

def z474 : W := mkw 0xc01ff5ff54800000 0xf803febfea900000 0xffbfffffe7c00001 0x1ff7fffffcf80000

def z475 : W := mkw 0x2028ec000a3a0000 0xc4051d8001474000 0x1da6b80007338003 0x63b4d70000e67000

def z476 : W := mkw 0x4015249040000000 0x4802a49208000000 0x0001061060000000 0x000020c20c000000

def z477 : W := mkw 0x02001005800084a4 0x00400200b0001094 0x8000000d800000e0 0x10000001b000001c

def z478 : W := mkw 0x0015080002120000 0x0002a10000424000 0x1fbfb80007338003 0x63f7f70000e67000

def z479 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0000086 0x3ff3fffffc000010

def z480 : W := mkw 0xd11ff7ffe045858a 0xfa23fefffc08b0b1 0x015eb9cc00cf8f9f 0xa02bd7398019f1f3

def z481 : W := mkw 0xac0ac16a09285850 0xb581582d41250b0a 0xeffec1ee1f3c7cff 0xfdffd83dc3e78f9f

def z482 : W := mkw 0x31350a00beff858a 0x0626a14017dff0b1 0x67ff00301fff8f9f 0xecffe00603fff1f3

def z483 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xffbfffce1ffff063 0xfff7fff9c3fffe0c

def z484 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0x011eb9cc18307060 0x4023d73983060e0c

def z485 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xffe7ff3fe733cfff 0x7ffcffe7fce679ff

def z486 : W := mkw 0xc01ff5ff54800000 0xf803febfea900000 0xffbfffffff000000 0x5ff7ffffffe00000

def z487 : W := mkw 0xc81735ff55806a00 0x7902e6bfeab00d40 0xf4673fffe7c07f05 0x1e8ce7fffcf80fe0

def z488 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0x0020000007c38f01 0x0004000000f871e0

def z489 : W := mkw 0x511737b5e045858a 0x6a22e6f6bc08b0b1 0xfec77e33e0cf8f9f 0xbfd8efc67c19f1f3

def z490 : W := mkw 0xa400004a08281050 0x148000094105020a 0xe3d801ce183c70fe 0xfc7b0039c3078e1f

def z491 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0xa000012fe0004cfc 0x14000025fc00099f

def z492 : W := mkw 0x2008c00008280000 0x8401180001050000 0xebd8c002183c009e 0xfd7b180043078013

def z493 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0xa000013de0004fe4 0x14000027bc0009fc

def z494 : W := mkw 0xae0ad16f8928dcf4 0xb5c15a2df1251b9e 0xa800c12f803c4cfe 0x15001825f007899f

def z495 : W := mkw 0x0a02112501004824 0x21404224a0200904 0x0000010c00004060 0x000000218000080c

def z496 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x179f3e31e0000000 0x02f3e7c63c000000

def z497 : W := mkw 0xc01ff5ff54802200 0xf803febfea900440 0xffdffffff8c03f05 0xbffbffffff1807e0

def z498 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x017eb9cc1ffff0ff 0xe02fd73983fffe1f

def z499 : W := mkw 0x4015340540000000 0x4802a680a8000000 0x14073e01e0000000 0x0280e7c03c000000

def z500 : W := mkw 0xd108f64fe045858a 0xda211ec9fc08b0b1 0xfec1fe3fe0cf8f9f 0xbfd83fc7fc19f1f3

def z501 : W := mkw 0x0815009015806a00 0x0102a01202b00d40 0x427900d01fc03f01 0x884f201a03f807e0

def z502 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe840c1ce003c70fe 0x1d081839c0078e1f

def z503 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x63fe01c01fc07f05 0xec7fc03803f80fe0

def z504 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x8958c1ce183c70fe 0xf12b1839c3078e1f

def z505 : W := mkw 0x11200a00b6d7858a 0x0224014016daf0b1 0x0060000007cf8f9f 0xa00c000000f9f1f3

def z506 : W := mkw 0x4a0211b5c100cca4 0x29404236b8201994 0xa000013de0004ce4 0x14000027bc00099c

def z507 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0x9800fe03e0000000 0x13001fc07c000000

def z508 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xeb98c1ce00000000 0x1d731839c0000000

def z509 : W := mkw 0xb428ee4a0a7f1050 0xd6851dc9414fe20a 0xfbd8ffce183ff0fe 0xff7b1ff9c307fe1f

def z510 : W := mkw 0x3028ee000a7f0000 0xc6051dc0014fe000 0x1da6fe00073f8003 0x63b4dfc000e7f000

def z511 : W := mkw 0x111de600a045858a 0xc223bcc01408b0b1 0xffdffe33e0cf8f9f 0xbffbffc67c19f1f3

def z512 : W := mkw 0xc00af5ff40000000 0xf8015ebfe8000000 0xfd86ffffe0000000 0x1fb0dffffc000000

def z513 : W := mkw 0x0815000015806a00 0x0102a00002b00d40 0x67ff01c01fc07f05 0xecffe03803f80fe0

def z514 : W := mkw 0x0000080002120000 0x0000010000424000 0x0126b80007300000 0x4024d70000e60000

def z515 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe7ff3fe73fccff 0xfffcffe7fce7f99f

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z517 : W := mkw 0x191703b0b5c5ef8a 0x2322e07616b8bdf1 0x993e47c3ff0ff09a 0x5327c8f87fe1fe13

def z518 : W := mkw 0xf03dee4a5eff0000 0xde07bdc94bdfe000 0x1fbffe027fff8003 0xe3f7ffc04ffff000

def z519 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0xfed946f3f8cfbf9f 0xbfdb28de7f19f7f3

def z520 : W := mkw 0xc808f44f55806a00 0xd9011e89eab00d40 0x9860fe0fffc07f05 0xf30c1fc1fff80fe0

def z521 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xebfef9ce1ffff0ff 0xfd7fdf39c3fffe1f

def z522 : W := mkw 0x0000080002120000 0x0000010000424000 0xffa7fe33e7338003 0x7ff4ffc67ce67000

def z523 : W := mkw 0x481735b541004800 0x6902e6b6a8200900 0x14273e31e7000c01 0x0284e7c63ce00180

def z524 : W := mkw 0x1b171bb5b7d7efae 0x2362e376b6fafdf5 0xffffffffffffffff 0xffffffffffffffff

def z525 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x173ffe001fff8001 0xc2e7ffc003fff000

def z526 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffd8c1ce183ff0ff 0xfffb1839c307fe1f

def z527 : W := mkw 0x303dee901eff2200 0xc607bdd203dfe440 0x7fffffd01ffff307 0xeffffffa03fffe60

def z528 : W := mkw 0x11352e00b6d7858a 0x4226a5c016daf0b1 0x14273e31e7c38f01 0x0284e7c63cf871e0

def z529 : W := mkw 0xb528ee4aaa7f95da 0xd6a51dc9554ff2bb 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000010c000040e4 0x140000218000081c

def z531 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x0bbef8001fff8003 0xe177df0003fff000

def z532 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x153f3e001fc38001 0x42a7e7c003f87000

def z533 : W := mkw 0x401735b554800000 0x6802e6b6aa900000 0x17bf3e31ffc00001 0xe2f7e7c63ff80000

def z534 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe001fffc0e7 0xe3f7ffc003fff81c

def z535 : W := mkw 0xc01df44f40000000 0xd803be89e8000000 0xff9fffcfe0000000 0x1ff3fff9fc000000

def z536 : W := mkw 0xb428ee4a0a7f1050 0xd6851dc9414fe20a 0xfffeffce1f3ff0ff 0xffffdff9c3e7fe1f

def z537 : W := mkw 0x0a1719b517926a24 0x2142e336a2f24d44 0x67ffb9fc1ff07f65 0xecfff73f83fe0fec

def z538 : W := mkw 0xa408e44a08281050 0xd4811c894105020a 0xfbd8ffce183c70fe 0xff7b1ff9c3078e1f

def z539 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x013eb8001f3f8002 0x4027d70003e7f000

def z540 : W := mkw 0x35200a00beff95da 0x06a4014017dff2bb 0x006000001fffffff 0xe00c000003ffffff

def z541 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffff007c05 0x7ff7ffffffe00f80

def z542 : W := mkw 0x001de40000000000 0xc003bc8000000000 0xff9ffe33e0000000 0x1ff3ffc67c000000

def z543 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0x1fbffe001fff80fb 0xe3f7ffc003fff01f

def z544 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff83c7078 0xdffbffffff078e0f

def z545 : W := mkw 0xce0211ffc100dcf4 0x39c0423ff8201b9e 0xe04001ffe0007cfc 0x1c08003ffc000f9f

def z546 : W := mkw 0xa508c04aa82895da 0x94a11809550512bb 0xebd8c1fff83c7ffe 0xfd7b183fff078fff

def z547 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1dbfbe001ff38003 0x63b7f7c003fe7000

def z548 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xbc814633e0cf8f9f 0x379028c67c19f1f3

def z549 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0x991effcff83c70fa 0x5323dff9ff078e1f

def z550 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9c01fe3fe0000000 0x13803fc7fc000000

def z551 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x14273e0007ff8003 0x0284e7c000fff000

def z552 : W := mkw 0x11352e00b6d7858a 0x4226a5c016daf0b1 0xfee77e33e7cf8f9f 0xbfdcefc67cf9f1f3

def z553 : W := mkw 0x191703b035c56b0a 0x2322e07606b8ad61 0x67ff47f27fcc7f1d 0xecffe8fe4ff98fe3

def z554 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffd8c1ef983c70fe 0xfffb183df3078e1f

def z555 : W := mkw 0xc01ff5ff40002200 0xf803febfe8000440 0xffdfffffe0003300 0x1ffbfffffc000660

def z556 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xfe9f7ef3e0000000 0x1fd3efde7c000000

def z557 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1c27fe0007ff8003 0x0384ffc000fff000

def z558 : W := mkw 0x001de40014800000 0xc003bc8002900000 0x1fbffe001fc00001 0xe3f7ffc003f80000

def z559 : W := mkw 0xf83fffff5fff6a00 0xff07ffffebffed40 0xffffffffffffff07 0xffffffffffffffe0

def z560 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x141f3ef1e0000000 0x0283e7de3c000000

def z561 : W := mkw 0x3028ee000a7f0000 0xc6051dc0014fe000 0x1926fe00073f8002 0x4324dfc000e7f000

def z562 : W := mkw 0x11150290b4c5a78a 0x0222a0521698b4f1 0xfed946f3f8cfbf9f 0xbfdb28de7f19f7f3

def z563 : W := mkw 0xae0ad96f8b3adcf4 0xb5c15b2df1675b9e 0x567e78e39f0fbc19 0x8acfcf1c73e1f783

def z564 : W := mkw 0x02001805821284a4 0x00400300b0425094 0x9926b80d873380e2 0x5324d701b0e6701c

def z565 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdffffff83070e6 0xfffbffffff060e1c

def z566 : W := mkw 0x511737b5e045858a 0x6a22e6f6bc08b0b1 0x14073e31e0c38f01 0x0280e7c63c1871e0

def z567 : W := mkw 0x201de40008280000 0xc403bc8001050000 0x1f9ffe00183c0002 0xe3f3ffc003078000

def z568 : W := mkw 0x2400000008281050 0x048000000105020a 0x63d801c0183c70fe 0xec7b003803078e1f

def z569 : W := mkw 0x0000080002120000 0x0000010000424000 0x1fa7b80007f38003 0xe3f4f70000fe7000

def z570 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9ffffff8003000 0x1ff3ffffff000600

def z571 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xefd8c1ee183c7cff 0xfdfb183dc3078f9f

def z572 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x2000012180004c04 0x0400002430000980

def z573 : W := mkw 0x0000080002120000 0x0000010000424000 0x1da6b8000733c0e7 0x63b4d70000e6781c

def z574 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda7bf3de733cce7 0x77b4f7e7bce6799c

def z575 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x14273e31e7000000 0x0284e7c63ce00000

def z576 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xffffb9fd9fc07f05 0xfffff73fb3f80fe0

def z577 : W := mkw 0x0000080002120000 0x0000010000424000 0x1526b80007338001 0x42a4d70000e67000

def z578 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfe814633e0c38f01 0x1fd028c67c1871e0

def z579 : W := mkw 0xee1ffdffcb3adcf4 0xfdc3ffbff9675b9e 0xffffffffff3ffcff 0xffffffffffe7ff9f

def z580 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x76873e31e0000000 0x0ed0e7c63c000000

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x88004002000c009a 0x1100080040018013

def z582 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x425900f018c03f00 0x884b201e031807e0

def z583 : W := mkw 0x0000080082128480 0x0000010010425090 0xbda6b82187338c87 0x77b4d70430e67190

def z584 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x0126b90c0733c063 0x6024d72180e6780c

def z585 : W := mkw 0x0a0211b58100eea4 0x21404236b0201dd4 0xa00001ed80007ce4 0x1400003db0000f9c

def z586 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0xe0400033e0000f9c 0x1c0800067c0001f3

def z587 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xffffbffdffc07f05 0xfffff7ffbff80fe0

def z588 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1c277e0007cf8003 0x0384efc000f9f000

def z589 : W := mkw 0x110002002045010a 0x022000400408a021 0x4241461260cc0318 0x884828c24c198063

def z590 : W := mkw 0x481725b055806a00 0x6902e4b60ab00d40 0x67ff07f07fc07f05 0xecffe0fe0ff80fe0

def z591 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xeac0400200cf8f9f 0xbd5808004019f1f3

def z592 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1da7fe0007ff8003 0x63b4ffc000fff000

def z593 : W := mkw 0xbe3fff6f9fffdcf4 0xf7c7ffedf3fffb9e 0xffffffef9ffffcff 0xfffffffdf3ffff9f

def z594 : W := mkw 0xe40af56f48281050 0xfc815eade905020a 0xbd86ff2fe03c40fe 0x77b0dfe5fc07881f

def z595 : W := mkw 0x3028ee001eff0000 0xc6051dc003dfe000 0x1da6fe001fff8003 0xe3b4dfc003fff000

def z596 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x9c07be3de0000000 0x1380f7c7bc000000

def z597 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x011881cc183c70fa 0x4023103983078e1f

def z598 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0x0060000007ffcfff 0xe00c000000fff9ff

def z599 : W := mkw 0xe41df4df48281050 0xdc83be9be905020a 0xda59fedff83c30fa 0x9b4b3fdbff07861f

def z600 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0x1c07fe31e0000000 0x0380ffc63c000000

def z601 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x153fbffdffc07f01 0x42a7f7ffbff80fe0

def z602 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1ffffe001fff8f07 0xe3ffffc003fff1e0

def z603 : W := mkw 0xe40af5ff48281050 0xfc815ebfe905020a 0xfbd8fffff83c70fe 0xff7b1fffff078e1f

def z604 : W := mkw 0x39200a00bfffef8a 0x0724014017fffdf1 0x006000001fffff9f 0xe00c000003fffff3

def z605 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0xfee77e0207cf809f 0xbfdcefc040f9f013

def z606 : W := mkw 0x13001a05a25785ae 0x02600340b44af0b5 0xfec1fe3fe0ff8fff 0xbfd83fc7fc1ff1ff

def z607 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xfde6b9ed8733fce7 0x7fbcd73db0e67f9c

def z608 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x66ff00f01fc03f05 0xacdfe01e03f807e0

def z609 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xfe87fe3fe0000000 0x1fd0ffc7fc000000

def z610 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbde6b92d9f33fce7 0xf7bcd725b3e67f9c

def z611 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1ea77e0007c38001 0x03d4efc000f87000

def z612 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x9f9ffe03e0000000 0x13f3ffc07c000000

def z613 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0x9918ffcff8307060 0x53231ff9ff060e0c

def z614 : W := mkw 0x800ad16f00000000 0xb0015a2de0000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z615 : W := mkw 0x8400004a00001050 0x108000094000020a 0xe3d801ce180070fc 0xfc7b0039c3000e1f

def z616 : W := mkw 0x2a0ad1258928cca4 0xa5415a24b1251994 0xab98c12d983c4ce6 0xf5731825b307899c

def z617 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x0000b80c00000000 0x0000170180000000

def z618 : W := mkw 0x02001805821284a4 0x00400300b0425094 0xb980b90d8033c0e6 0x77301721b006781c

def z619 : W := mkw 0x0000080002120000 0x0000010000424000 0x1c26b80007338003 0x0384d70000e67000

def z620 : W := mkw 0x34200a001eff1050 0x0684014003dfe20a 0xbde6b90c1ffff0ff 0xf7bcd72183fffe1f

def z621 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xffdfffffe00c70fe 0xbffbfffffc018e1f

def z622 : W := mkw 0x13001a05a25785ae 0x02600340b44af0b5 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z623 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x14273e001fcf8001 0x8284e7c003f9f000

def z624 : W := mkw 0xc00211ff40000000 0x3800423fe8000000 0xfe8147ffe0000000 0x1fd028fffc000000

def z625 : W := mkw 0x0a1711b59580eea4 0x2142e236b2b01dd4 0xe7ff01fd9fc07fe5 0xfcffe03fb3f80ffc

def z626 : W := mkw 0xf03deeda5eff0000 0xde07bddb4bdfe000 0xffbffef3ffff8003 0xfff7ffde7ffff000

def z627 : W := mkw 0x0815009015806a00 0x0102a01202b00d40 0x47ff00d01fc07f05 0xe8ffe01a03f80fe0

def z628 : W := mkw 0xc01decda42120000 0xd803bd9b48424000 0x5fbffed267338003 0x6bf7ffda4ce67000

def z629 : W := mkw 0xf43de6da5ced1050 0xde87bcdb4b9da20a 0x425946d278cc3018 0x884b28da4f198603

def z630 : W := mkw 0x0000080002120000 0x0000010000424000 0x1fa6f800073f8003 0xe3f4df0000e7f000

def z631 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x9d1fffffe0000000 0x13a3fffffc000000

def z632 : W := mkw 0xc01ff5ff54802200 0xf803febfea900440 0xff9ffffff8003000 0x1ff3ffffff000600

def z633 : W := mkw 0xc01ff56f40000000 0xf803feade8000000 0xbf9fff2fe0000000 0x17f3ffe5fc000000

def z634 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0xfec1fe3fe03c00fe 0xbfd83fc7fc07801f

def z635 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xff9ffffff80c0000 0x9ff3ffffff018000

def z636 : W := mkw 0x001ff52500000000 0xe003fea4a0000000 0xff9fff3fe0000000 0x1ff3ffe7fc000000

def z637 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xcb58c1ce183c70fa 0xd96b1839c3078e1f

def z638 : W := mkw 0x8408c04a00001050 0x908118094000020a 0xebd8c1ce000070fc 0x1d7b1839c0000e1f

def z639 : W := mkw 0x4015349540000000 0x4802a692a8000000 0x10013e11e0000000 0x020027c23c000000

def z640 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1527be0007f38001 0x42a4f7c000fe7000

def z641 : W := mkw 0x10202e0002570000 0x420405c0004ae000 0x14263e0007038001 0x0284c7c000e07000

def z642 : W := mkw 0xb43de6da1ced3250 0xd687bcdb439da64a 0x425946d218cc3318 0x884b28da43198663

def z643 : W := mkw 0x0802012001004800 0x2100402400200900 0x67fe01e01f007c05 0xecffc03c03e00f80

def z644 : W := mkw 0x0015009014802200 0x0002a01202900440 0x001800c018003000 0x0003001803000600

def z645 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0xbda7bf0c07f3c0e7 0x77b4f7e180fe781c

def z646 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffbfffffe7000001 0x7ff7fffffce00000

def z647 : W := mkw 0x0000080002120000 0x0000010000424000 0x15a6380007038001 0x62b4c70000e07000

def z648 : W := mkw 0x0002112500000000 0x20004224a0000000 0x14073e31e0000000 0x0280e7c63c000000

def z649 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9800fe0fe00c009a 0x13001fc1fc018013

def z650 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x0040000000cf8f9f 0xa00800000019f1f3

def z651 : W := mkw 0x0015080016920000 0x0002a10002d24000 0x1427380007c38001 0x0284e70000f87000

def z652 : W := mkw 0xa41fc1fa08281050 0xb483f83f4105020a 0xefdfc1fe183c70fe 0xfdfbf83fc3078e1f

def z653 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xffdfffffe0003018 0x1ffbfffffc000603

def z654 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0xff9ffef3e0000000 0x1ff3ffde7c000000

def z655 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xff9fffffe00000f8 0x1ff3fffffc00001f

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0x14010631e0000000 0x028020c63c000000

def z657 : W := mkw 0xe01ff5ff5ca80000 0xfc03febfeb950000 0xffbffffffffc0003 0xfff7ffffffff8000

def z658 : W := mkw 0x0002112500000000 0x20004224a0000000 0xa000012d80000000 0x14000025b0000000

def z659 : W := mkw 0xca1ff5ffc100cca4 0xf943febff8201994 0xff9fffffe0004ce4 0x1ff3fffffc00099c

def z660 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x1fbffe001f338003 0x63f7ffc003e67000

def z661 : W := mkw 0x2a3ffd259fbacca4 0xe547ffa4b3f75994 0xbdbeb92d9f33cce7 0x77b7d725b3e6799c

def z662 : W := mkw 0x3028ca001eff0000 0x8605194003dfe000 0x0bb8c0001fff8003 0xe177180003fff000

def z663 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xebd8c1ce18007004 0xfd7b1839c3000e00

def z664 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xffbffe021fff8003 0xfff7ffc043fff000

def z665 : W := mkw 0x0802012001004800 0x2100402400200900 0xada6812c07304ce7 0x75b4d02580e6099c

def z666 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xbda6b93de733cfe7 0x77b4d727bce679fc

def z667 : W := mkw 0xa41dc0da1ca83250 0x9483b81b4395064a 0x425940d218cc3318 0x884b281a43198663

def z668 : W := mkw 0x4a0219b5c312cca4 0x29404336b8625994 0xbda6b93de733cce7 0x77b4d727bce6799c

def z669 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9d86fe0fe0000000 0x13b0dfc1fc000000

def z670 : W := mkw 0x02001805821284a4 0x00400300b0425094 0x9c26b80d873380e3 0x1384d701b0e6701c

def z671 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0xdf9ffedfe0000000 0x1bf3ffdbfc000000

def z672 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x5ffffec01fffb003 0xebffffd803fff600

def z673 : W := mkw 0x081709b017926a00 0x2102e13602f24d40 0xffffb9fc1ff3ffe7 0xfffff73f83fe7ffc

def z674 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff83c301a 0xfffbffffff078603

def z675 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff01f01ff07fe7 0xecffe03e03fe0ffc

def z676 : W := mkw 0x0000000080008480 0x0000000010001090 0xa000002180000c84 0x1400000430000190

def z677 : W := mkw 0x1b021325a145cdae 0x23604264b428b9b5 0xfec1473fe0cfcfff 0xbfd828e7fc19f9ff

def z678 : W := mkw 0x313de6003ced010a 0xc627bcc0079da021 0x4259461278cc0318 0x884b28c24f198063

def z679 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1da6b92d8733cc63 0x63b4d725b0e6798c

def z680 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xefff01f01fc07f87 0xfdffe03e03f80ff0

def z681 : W := mkw 0x3028ee000a7f0000 0xc6051dc0014fe000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z682 : W := mkw 0xcc1ff5ff55807a50 0xf983febfeab00f4a 0xffffffffffc07ffd 0xfffffffffff80fff

def z683 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x1fbffe021fff801b 0xe3f7ffc043fff003

def z684 : W := mkw 0x10202e0002570000 0x420405c0004ae000 0x1da6be0007338003 0x63b4d7c000e67000

def z685 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xbfbfff0c1fff8003 0xf7f7ffe183fff000

def z686 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7ffffff01fffff07 0xeffffffe03ffffe0

def z687 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x017801c01fc07f05 0xe02f003803f80fe0

def z688 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x467f00f01fc07f05 0xe8cfe01e03f80fe0

def z689 : W := mkw 0x02001805821284a4 0x00400300b0425094 0xbda6b82d87338ce7 0x77b4d705b0e6719c

def z690 : W := mkw 0xae08c84a8b3adcf4 0x95c1190951675b9e 0xebf8c1ce1f3ffcff 0xfd7f1839c3e7ff9f

def z691 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x571fffffe0000000 0x0ae3fffffc000000

def z692 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x6fff81f01ff07f07 0xedfff03e03fe0fe0

def z693 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xe000013fe0004ce4 0x1c000027fc00099c

def z694 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbfa7ff2d8733cce7 0x77f4ffe5b0e6799c

def z695 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xffdfffffe00070fc 0x1ffbfffffc000e1f

def z696 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffe74633e7cf8f9f 0xfffce8c67cf9f1f3

def z697 : W := mkw 0x303dee901eff2200 0xc607bdd203dfe440 0x1fbffe101fff8303 0xe3f7ffc203fff060

def z698 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x10263e0007038000 0x0204c7c000e07000

def z699 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe31ffff8003 0xe3f7ffc63ffff000

def z700 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xa126b92d87304ce4 0x5424d725b0e6099c

def z701 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x25a6b92c07304c65 0x64b4d72580e6098c

def z702 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xb4073f3de0000000 0x1680e7e7bc000000

def z703 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x1d87be31e0000000 0x03b0f7c63c000000

def z704 : W := mkw 0xc00af56f40000000 0xf8015eade8000000 0xff9effefe0000000 0x1ff3dffdfc000000

def z705 : W := mkw 0x0815009015806a00 0x0102a01202b00d40 0x63f901d01fc07f05 0xec7f203a03f80fe0

def z706 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x561f3ef1e0000000 0x0ac3e7de3c000000

def z707 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec1473fe0cfcfff 0xbfd828e7fc19f9ff

def z708 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1e3ffe001fff8003 0x83c7ffc003fff000

def z709 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x193efe001fff8003 0xe327dfc003fff000

def z710 : W := mkw 0x0000080002120000 0x0000010000424000 0x1fbeb8001f338003 0xe3f7d70003e67000

def z711 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0x52197ed3e0000000 0x0a432fda7c000000

def z712 : W := mkw 0x0200180502120024 0x00400300a0424004 0x1da6b80c07338063 0x63b4d70180e6700c

def z713 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0xfe9946f3e0000000 0x1fd328de7c000000

def z714 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xbc80012d80004ce4 0x17900025b000099c

def z715 : W := mkw 0x0000000000000000 0x0000000000000000 0x639801c000000000 0x0c73003800000000

def z716 : W := mkw 0x181703b015c56a00 0x2302e07602b8ad40 0x7fff47f01fcfff07 0xefffe8fe03f9ffe0

def z717 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xda01fe1fe0000000 0x1b403fc3fc000000

def z718 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda7b93d87f3cfe7 0x77b4f727b0fe79fc

def z719 : W := mkw 0xb508c24a286d115a 0x96a11849450da22b 0x425946d278cc3318 0x884b28da4f198663

def z720 : W := mkw 0x02000800821284a4 0x0040010010425094 0x8800800c003380e2 0x110010018006701c

def z721 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdfffffe03c00fe 0xbffbfffffc07801f

def z722 : W := mkw 0xc00af56f40000000 0xf8015eade8000000 0xb800ff2fe0000000 0x17001fe5fc000000

def z723 : W := mkw 0x8e02116f8100dcf4 0x31c0422df0201b9e 0xa000012f80004cfc 0x14000025f000099f

def z724 : W := mkw 0x0015009014802200 0x0002a01202900440 0x63d901d018c07304 0xec7b203a03180e60

def z725 : W := mkw 0x0802092003124800 0x2100412400624900 0xbda6b92c0733cce7 0x77b4d72580e6799c

def z726 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xbda6b92fe733ccff 0x77b4d725fce6799f

def z727 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff00301fc00f05 0xecffe00603f801e0

def z728 : W := mkw 0x0000000080008480 0x0000000010001090 0xbd80812d8033cce7 0x77b01025b006799c

def z729 : W := mkw 0xb408c24a086d1050 0x96811849410da20a 0xffd9c7ce18fff0ff 0xfffb38f9c31ffe1f

def z730 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x9c414633e0cf8f9f 0xb38828c67c19f1f3

def z731 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe00c0018 0x9ffbfffffc018003

def z732 : W := mkw 0xa41de44a08281050 0xd483bc894105020a 0xffdffffff83c70fe 0xfffbffffff078e1f

def z733 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff41f21fcc7f1d 0xecffe83e43f98fe3

def z734 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe15881ce183070fc 0x5c2b1039c3060e1f

def z735 : W := mkw 0x8008c04a00000000 0x9001180940000000 0x8800c00e00000000 0x11001801c0000000

def z736 : W := mkw 0x10000a0002570000 0x02000140004ae000 0x1ea77e0007cf8003 0xa3d4efc000f9f000

def z737 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbc26b92d8733cce7 0x1784d725b0e6799c

def z738 : W := mkw 0x001701b000000000 0x2002e03600000000 0xff9f47f3e0000000 0x1ff3e8fe7c000000

def z739 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xff9f7ff3e0000000 0x1ff3effe7c000000

def z740 : W := mkw 0xb53de64a3ced115a 0xd6a7bcc9479da22b 0x425946d278cc3318 0x884b28da4f198663

def z741 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xa99881cc183070e6 0x7533103983060e1c

def z742 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9ffffff8000000 0xfff3ffffff000000

def z743 : W := mkw 0x0000000000000000 0x0000000000000000 0xeec1403200cc0f9f 0xbdd82806401981f3

def z744 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0xebe0c10e07ffcfff 0xfd7c1821c0fff9ff

def z745 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffa6f92f8733cce7 0x7ff4df25f0e6799c

def z746 : W := mkw 0xe408e44a48281050 0xdc811c894905020a 0xebd8c7ce783c70fe 0xfd7b18f9cf078e1f

def z747 : W := mkw 0x3b3fff25bfffcdae 0xe767ffe4b7fff9b5 0xffffff3fffffcfff 0xffffffe7fffff9ff

def z748 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x153fbe001fff8003 0xe2a7f7c003fff000

def z749 : W := mkw 0x30350a001eff0000 0x0606a14003dfe000 0x1fbfb8001fff8003 0xe3f7f70003fff000

def z750 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b82187338003 0x77b4d70430e67000

def z751 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x193eb8001f338002 0x4327d70003e67000

def z752 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x193efe001f3f8002 0x4327dfc003e7f000

def z753 : W := mkw 0x110002002045010a 0x022000400408a021 0xeac1461260cc039e 0xbd5828c24c198073

def z754 : W := mkw 0x2400000008281050 0x048000000105020a 0xa9c0810c183c70fe 0xf538102183078e1f

def z755 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec1c63fe0ff8fff 0xbfd838c7fc1ff1ff

def z756 : W := mkw 0xc81fe5fa55806a00 0xf903fcbf4ab00d40 0x67ff47f27fc07f05 0xecffe8fe4ff80fe0

def z757 : W := mkw 0x110002002045010a 0x022000400408a021 0x5ec1461260cf831b 0xabd828c24c19f063

def z758 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x17bf7e001fcf8001 0xe2f7efc003f9f000

def z759 : W := mkw 0x8400084a02121050 0x108001094042420a 0xfde6b9ce0733f0ff 0x7fbcd739c0e67e1f

def z760 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14633e00c009e 0xbfd828c67c018013

def z761 : W := mkw 0xf51ff7ffe86d95da 0xfea3fefffd0db2bb 0xffdffffff8ffffff 0xfffbffffff1fffff

def z762 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff01c01fc07005 0xecffe03803f80e00

def z763 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x76c14633e0cf8f1d 0xaed828c67c19f1e3

def z764 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe6b92d8733cce7 0xfffcd725b0e6799c

def z765 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x627901f01fc07f05 0xec4f203e03f80fe0

def z766 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd8c1ce180c3018 0x9d7b1839c3018603

def z767 : W := mkw 0x0a02192503124824 0x21404324a0624904 0xbda6b92d87304060 0x57b4d725b0e6080c

def z768 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda6ff2fe733cce7 0x77b4dfe5fce6799c

def z769 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffd9c7fff8fc7fff 0xfffb38ffff1f8fff

def z770 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe358c1ce183c70fc 0xdc6b1839c3078e1f

def z771 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x7fff47f01fc07f05 0xefffe8fe03f80fe0

def z772 : W := mkw 0x0000080002120000 0x0000010000424000 0x002000000733c0e7 0x6004000000e6781c

def z773 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x421946f3e0000000 0x084328de7c000000

def z774 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffc14733e0cfcf9f 0xfff828e67c19f9f3

def z775 : W := mkw 0x1000020000450000 0x020000400008a000 0x7ec1463000cf8f07 0xafd828c60019f1e0

def z776 : W := mkw 0x2008c00008280000 0x8401180001050000 0x6bd8c1c0183c7006 0xed7b183803078e00

def z777 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xfa80fe0fe0000000 0x1f501fc1fc000000

def z778 : W := mkw 0x0a0219258312eea4 0x21404324b0625dd4 0xbde6b92d8733ffe7 0x77bcd725b0e67ffc

def z779 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa000012d80304ce6 0x74000025b006099c

def z780 : W := mkw 0xc40211ff40001050 0x3880423fe800020a 0xe04001ffe00070fc 0x1c08003ffc000e1f

def z781 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14633e0c00f05 0xbfd828c67c1801e0

def z782 : W := mkw 0xa41dc84a1eba1050 0x9483b90943d7420a 0xfffff9ce1ffff0ff 0xffffff39c3fffe1f

def z783 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x9fbfffce1ffff0fb 0xf3f7fff9c3fffe1f

def z784 : W := mkw 0xc00af56f40000000 0xf8015eade8000000 0x9c06fe2fe0000000 0x1380dfc5fc000000

def z785 : W := mkw 0x1000020000450000 0x020000400008a000 0xfe814633e0cf8003 0xbfd028c67c19f000

def z786 : W := mkw 0xc80af56f41004800 0xf9015eade8200900 0xbda6ff2fe7004c05 0x77b4dfe5fce00980

def z787 : W := mkw 0xb43de64a1ced1050 0xd687bcc9439da20a 0x0219460218cc0018 0x804328c043198003

def z788 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x67ffb9fc1fc07f05 0xecfff73f83f80fe0

def z789 : W := mkw 0x0a02192503124824 0x21404324a0624904 0xbda6b90c0733c0e7 0x77b4d72180e6781c

def z790 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x5f9ffef3e0000000 0x0bf3ffde7c000000

def z791 : W := mkw 0x0015080016920000 0x0002a10002d24000 0x1dbeb8001f338003 0x63b7d70003e67000

def z792 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0x9fbffe0e1fff8003 0xf3f7ffc1c3fff000

def z793 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c80000000038003 0x2390000000007000

def z794 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9da6b82d87338ce3 0x73b4d705b0e6719c

def z795 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x74073ff1e0000000 0x0e80e7fe3c000000

def z796 : W := mkw 0xc01ff5ff54802200 0xf803febfea900440 0xffdffffff8c07304 0xfffbffffff180e60

def z797 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xffff7ff3ffc07f05 0xffffeffe7ff80fe0

def z798 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xdb1fffdfe0000000 0x1b63fffbfc000000

def z799 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9918ffcfe0000000 0x13231ff9fc000000

def z800 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x63fe01c01f007004 0xec7fc03803e00e00

def z801 : W := mkw 0x38370bb01fff6a00 0x2706e17603ffed40 0x67ff01f01fffff07 0xecffe03e03ffffe0

def z802 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x88004002000f809a 0x110008004001f013

def z803 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xfffffe0e1fff80ff 0xffffffc1c3fff01f

def z804 : W := mkw 0x31200a00aa7f858a 0x06240140154ff0b1 0x0040000000ff8f9f 0xa0080000001ff1f3

def z805 : W := mkw 0x02021925821284a4 0x20404324b0425094 0xbd86b92d803380e2 0x17b0d725b006701c

def z806 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x057f01f01fc07f05 0xe0afe03e03f80fe0

def z807 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbdbeb9ed9f33fce7 0x77b7d73db3e67f9c

def z808 : W := mkw 0x303de6901ced2200 0xc607bcd2039da440 0x425946d018cc3300 0x884b28da03198660

def z809 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x013e39c01f007000 0x4027c73803e00e00

def z810 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0xfe99feffe0000000 0x1fd33fdffc000000

def z811 : W := mkw 0xa408c84a0a3a1050 0x948119094147420a 0x5ffef8c21f3fb01b 0xebffdf1843e7f603

def z812 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xefff81fc1fc07f05 0xfdfff03f83f80fe0

def z813 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x5ec14633e0cf8f1b 0xabd828c67c19f1e3

def z814 : W := mkw 0x201de40008280000 0xc403bc8001050000 0xffdffe33f83c009e 0xfffbffc67f078013

def z815 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffffc07300 0xdffffffffff80e60

def z816 : W := mkw 0x1a021b258357cca4 0x23404364b06af994 0xbfa7ff2d87ffcce7 0xf7f4ffe5b0fff99c

def z817 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7ffffe001fff8007 0xefffffc003fff000

def z818 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xfffef9ef9f3ffcff 0xffffdf3df3e7ff9f

def z819 : W := mkw 0x0000080002120000 0x0000010000424000 0x1da6b90c0733c063 0x63b4d72180e6780c

def z820 : W := mkw 0x0002112500000000 0x20004224a0000000 0xfe877e33e0000000 0x1fd0efc67c000000

def z821 : W := mkw 0xa40ad16f08281050 0xb4815a2de105020a 0xffdffffff83c70fe 0xfffbffffff078e1f

def z822 : W := mkw 0x1b021b25a357cdae 0x23604364b46af9b5 0xbda7bf3de7f3cfe7 0x77b4f7e7bcfe79fc

def z823 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xe3d801ed98007ce4 0xfc7b003db3000f9c

def z824 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xbda7bf3de7c04f05 0x77b4f7e7bcf809e0

def z825 : W := mkw 0x080201b001006a00 0x2100403600200d40 0x66c101f000c07f05 0xacd8203e00180fe0

def z826 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0x54073ef3e0000000 0x0a80e7de7c000000

def z827 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0xfee14633e7ffcfff 0xffdc28c67cfff9ff

def z828 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe0007ff8003 0x03f7ffc000fff000

def z829 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0xebc0c13fe03c4ffe 0xfd781827fc0789ff

def z830 : W := mkw 0x8400004a00001050 0x108000094000020a 0xe9c081ce003070fe 0x7d381039c0060e1f

def z831 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xe21947ffe0000000 0x1c4328fffc000000

def z832 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x47ff00f01fc03f01 0xe8ffe01e03f807e0

def z833 : W := mkw 0xf43deeda5eff1050 0xde87bddb4bdfe20a 0x5ffffed27fffb01b 0xebffffda4ffff603

def z834 : W := mkw 0x0002112500000000 0x20004224a0000000 0x1406382180000000 0x0280c70430000000

def z835 : W := mkw 0x0000080002120000 0x0000010000424000 0x1426380007338003 0x6284c70000e67000

def z836 : W := mkw 0x01000000a000858a 0x00200000140010b1 0xfec14633e0000f9c 0x1fd828c67c0001f3

def z837 : W := mkw 0x02001805821284a4 0x00400300b0425094 0xbda6b90d8733c0e7 0x77b4d721b0e6781c

def z838 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1ca73e0007c38003 0x2394e7c000f87000

def z839 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbde6b92d87f3cfe7 0xf7bcd725b0fe79fc

def z840 : W := mkw 0x0815000015806a00 0x0102a00002b00d40 0x07ff00001fc07f05 0xe0ffe00003f80fe0

def z841 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x143f3e001fc38001 0x0287e7c003f87000

def z842 : W := mkw 0xa400004a08281050 0x148000094105020a 0xe04001ce183c70fe 0xfc080039c3078e1f

def z843 : W := mkw 0x9108c24aa045858a 0x922118495408b0b1 0xffd9c7ffe0cf8f9f 0xbffb38fffc19f1f3

def z844 : W := mkw 0xac0ac1fa09287a50 0xb581583f41250f4a 0xebd8c1fe183c7ffe 0xfd7b183fc3078fff

def z845 : W := mkw 0x8f02116fa100ddfe 0x31e0422df4201bbf 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z846 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xfb9effcfe0000000 0x1f73dff9fc000000

def z847 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xff99c7ffe0000000 0x1ff338fffc000000

def z848 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec147f3e0cfff9f 0xbfd828fe7c19fff3

def z849 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe301fff8f03 0xe3f7ffc603fff1e0

def z850 : W := mkw 0x0a1719259792cca4 0x2142e324b2f25994 0xbfbfb92d9ff3cce7 0xf7f7f725b3fe799c

def z851 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x013eb8001f338003 0x6027d70003e67000

def z852 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1d3ffe001fff8003 0x43a7ffc003fff000

def z853 : W := mkw 0xc81ff5ff41006a00 0xf903febfe8200d40 0xff9fffffe0007000 0x1ff3fffffc000e00

def z854 : W := mkw 0x001dec0016920000 0xc003bd8002d24000 0x1fbffe001ff38003 0xe3f7ffc003fe7000

def z855 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0xffbfffffff307060 0x5ff7ffffffe60e0c

def z856 : W := mkw 0x8400004a00001050 0x108000094000020a 0x404000c200003018 0x0808001840000603

def z857 : W := mkw 0xaf0ad16fa928ddfe 0xb5e15a2df5251bbf 0xebd8c1fff83c7ffe 0xfd7b183fff078fff

def z858 : W := mkw 0xe41df44f48281050 0xdc83be89e905020a 0xffdfffcff83c70fe 0xfffbfff9ff078e1f

def z859 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xead840c2180c309e 0xbd5b081843018613

def z860 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x046700301fc07f05 0xe08ce00603f80fe0

def z861 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0x67ffb9fc1fc07f05 0xecfff73f83f80fe0

def z862 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x63d881cc18307064 0xec7b103983060e0c

def z863 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfc414633e0cf8f9f 0x1f8828c67c19f1f3

def z864 : W := mkw 0x0a0211b58100cca4 0x21404236b0201994 0xe00001fd80004ce4 0x1c00003fb000099c

def z865 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xfffffffffff07fe7 0xfffffffffffe0ffc

def z866 : W := mkw 0xe40ad1ff48281050 0xbc815a3fe905020a 0xebd8c1fff83c70fe 0xfd7b183fff078e1f

def z867 : W := mkw 0x001701b000000000 0x2002e03600000000 0x67df01f018007004 0xecfbe03e03000e00

def z868 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xfffffffe1fffffff 0xffffffffc3ffffff

def z869 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x76e73e3007c38f05 0xaedce7c600f871e0

def z870 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x76c73e31e0c00f05 0xaed8e7c63c1801e0

def z871 : W := mkw 0xec1ff5ff49285850 0xfd83febfe9250b0a 0xffffffffff3c7cff 0xffffffffffe78f9f

def z872 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0x5fbffec21fff8003 0xebf7ffd843fff000

def z873 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0038003 0x3ff3fffffc007000

def z874 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xfec1fe3fe0c00f05 0xbfd83fc7fc1801e0

def z875 : W := mkw 0x0000080016920000 0x0000010002d24000 0x1da6b8001ff38003 0xe3b4d70003fe7000

def z876 : W := mkw 0x10000a0002570000 0x02000140004ae000 0xffe7ff0e07ffc0ff 0xfffcffe1c0fff81f

def z877 : W := mkw 0x001711b500000000 0x2002e236a0000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z878 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xebd8c1ce000c009e 0xbd7b1839c0018013

def z879 : W := mkw 0x081701b09580ee80 0x2102e03612b01dd0 0xffff01f19fc3ff87 0xffffe03e33f87ff0

def z880 : W := mkw 0x0b0211b5a100efae 0x21604236b4201df5 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z881 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x1fffffcc1ffff0ff 0xe3fffff983fffe1f

def z882 : W := mkw 0x0000000000000000 0x0000000000000000 0xebd881cc183070e6 0xfd7b103983060e1c

def z883 : W := mkw 0x401735b554802200 0x6802e6b6aa900440 0x14073e31e0c00300 0x0280e7c63c180060

def z884 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xefd9c1ce18fc70ff 0xfdfb3839c31f8e1f

def z885 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x8840c00e183c70fe 0xf1081801c3078e1f

def z886 : W := mkw 0xc408f44f40001050 0xd8811e89e800020a 0x9800fe0fe00000f8 0x13001fc1fc00001f

def z887 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0c00001 0xbff3fffffc180000

def z888 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0xf79f3fffe0000000 0x1ef3e7fffc000000

def z889 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda6b92d8733c0e2 0x57b4d725b0e6781c

def z890 : W := mkw 0xc00af5ff40000000 0xf8015ebfe8000000 0xfe81ffffe0000000 0x1fd03ffffc000000

def z891 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x567f7ec21fcfb019 0x8acfefd843f9f603

def z892 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x1fbffe0c1fff8063 0xe3f7ffc183fff00c

def z893 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x77ff07f1ffc07f05 0xeeffe0fe3ff80fe0

def z894 : W := mkw 0xa40ad16f08281050 0xb4815a2de105020a 0xffdef9ef983c70fe 0xfffbdf3df3078e1f

def z895 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xfee77e33e7c00f05 0xbfdcefc67cf801e0

def z896 : W := mkw 0x0000080002120000 0x0000010000424000 0x7ffeb9c01f33f007 0xefffd73803e67e00

def z897 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff47f27fc07f05 0xecffe8fe4ff80fe0

def z898 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0xfe81fe33e0000000 0x1fd03fc67c000000

def z899 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdfffffe03c70fe 0x1ffbfffffc078e1f

def z900 : W := mkw 0x30200a000a7f0000 0x06040140014fe000 0x00000000003f8002 0x000000000007f000

def z901 : W := mkw 0xc80211ff41006a00 0x3900423fe8200d40 0xe04001ffe0007f04 0x1c08003ffc000fe0

def z902 : W := mkw 0x0015240000000000 0x4002a48000000000 0x14073e31e0000000 0x0280e7c63c000000

def z903 : W := mkw 0xa43dec4a1eba1050 0xd487bd8943d7420a 0xfffef9ce1f3ff0ff 0xffffdf39c3e7fe1f

def z904 : W := mkw 0xc81735ff55806a00 0x7902e6bfeab00d40 0xf7ff3fffffc07f05 0xfeffe7fffff80fe0

def z905 : W := mkw 0x303dee001eff2200 0xc607bdc003dfe440 0x1ffffe001fffb303 0xe3ffffc003fff660

def z906 : W := mkw 0x001701b014800000 0x2002e03602900000 0x67bf01f01fc00001 0xecf7e03e03f80000

def z907 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbfff0c1fffc063 0xe3f7ffe183fff80c

def z908 : W := mkw 0x0000000000000000 0x0000000000000000 0xebd8c1ce183c70fe 0xfd7b1839c3078e1f

def z909 : W := mkw 0xca0211ffc100eea4 0x3940423ff8201dd4 0xe04001ffe0007fe4 0x1c08003ffc000ffc

def z910 : W := mkw 0xf03de6da5ced0000 0xde07bcdb4b9da000 0x421946d278cc0000 0x884328da4f198000

def z911 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x153fbe0007c38001 0x02a7f7c000f87000

def z912 : W := mkw 0xc408f44f40001050 0xd8811e89e800020a 0xf840ffcfe00070fc 0x1f081ff9fc000e1f

def z913 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9ffffff83070e6 0x7ff3ffffff060e1c

def z914 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbfa6f92d873fcce7 0xf7f4df25b0e7f99c

def z915 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x9806fe0fe0000000 0x1300dfc1fc000000

def z916 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9ffffff8007000 0x5ff3ffffff000e00

def z917 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0x1fbffe027fff801b 0xe3f7ffc04ffff003

def z918 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x4358c1ce183c70fe 0xe86b1839c3078e1f

def z919 : W := mkw 0x8008c84a02120000 0x9001190940424000 0xffbef9ce07338003 0x7ff7df39c0e67000

def z920 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x5ffffe101fff8303 0xebffffc203fff060

def z921 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x14273e001fc38001 0xe284e7c003f87000

def z922 : W := mkw 0x401735b554800000 0x6802e6b6aa900000 0x14273e31e7c00001 0x0284e7c63cf80000

def z923 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1ebf7e001fcf8003 0xa3d7efc003f9f000

def z924 : W := mkw 0x0815009015806a00 0x0102a01202b00d40 0x66f900f01fc07f05 0xecdf201e03f80fe0

def z925 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0x0020000007f3cfe7 0x6004000000fe79fc

def z926 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x617e01f01fc07f05 0xec2fc03e03f80fe0

def z927 : W := mkw 0x11352e0036d7010a 0x4226a5c006dae021 0x56677e1267cf8319 0x8accefc24cf9f063

def z928 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xb9a6b90d8733c0e6 0x7734d721b0e6781c

def z929 : W := mkw 0x303dee901eff2200 0xc607bdd203dfe440 0x7ffffef01fffbf07 0xefffffde03fff7e0

def z930 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x9f9ffe3fe0000000 0x13f3ffc7fc000000

def z931 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x043f00f01fc03f01 0x0087e01e03f807e0

def z932 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x667f01f01fc07f05 0x8ccfe03e03f80fe0

def z933 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe0000f04 0x1ffbfffffc0001e0

def z934 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa480012d80004ce5 0x34900025b000099c

def z935 : W := mkw 0xc00af5ff40000000 0xf8015ebfe8000000 0xfb98ffffe0000000 0x1f731ffffc000000

def z936 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x7fff01f01fc3ff07 0xefffe03e03f87fe0

def z937 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x0026380007c38001 0x0004c70000f87000

def z938 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1b3ffe001fff8002 0xc367ffc003fff000

def z939 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0xffd9fffff83c70fe 0xfffb3fffff078e1f

def z940 : W := mkw 0x4008f40540000000 0xc8011e80a8000000 0x1800fe01e0000000 0x03001fc03c000000

def z941 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe00040e4 0x1ff3fffffc00081c

def z942 : W := mkw 0x0000000000000000 0x0000000000000000 0x05a6000007000001 0x60b4c00000e00000

def z943 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x1ea77e001fff8003 0xe3d4efc003fff000

def z944 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xffff01f19fc07f05 0xffffe03e33f80fe0

def z945 : W := mkw 0x8008c04a00000000 0x9001180940000000 0x011881cc00000000 0x0023103980000000

def z946 : W := mkw 0x481735b541004800 0x6902e6b6a8200900 0x35a73f31e7004c05 0x66b4e7e63ce00980

def z947 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0x94073e3fe0000000 0x1280e7c7fc000000

def z948 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe0007004 0x1ffbfffffc000e00

def z949 : W := mkw 0x703dee905eff0000 0xce07bdd20bdfe000 0x1fbffe107fff8003 0xe3f7ffc20ffff000

def z950 : W := mkw 0xc00235ff40000000 0x780046bfe8000000 0xf0003fffe0000000 0x1e0007fffc000000

def z951 : W := mkw 0x10200a0016d70000 0x0204014002dae000 0x1426380007c38001 0x0284c70000f87000

def z952 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0xfe877fffe0000000 0x1fd0effffc000000

def z953 : W := mkw 0x00352c0016920000 0x4006a58002d24000 0x1da6b80007338003 0x63b4d70000e67000

def z954 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xebdef9ce183c70fe 0xfd7bdf39c3078e1f

def z955 : W := mkw 0x101de60014c50000 0xc203bcc00298a000 0x1fbffe001fcf8003 0xe3f7ffc003f9f000

def z956 : W := mkw 0xa41dc04a1ca81050 0x9483b8094395020a 0xefffc1ce1ffc70ff 0xfdfff839c3ff8e1f

def z957 : W := mkw 0xc00af5ff40000000 0xf8015ebfe8000000 0x9800fe3fe0000000 0x13001fc7fc000000

def z958 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x14014633e0cf8f19 0x028028c67c19f1e3

def z959 : W := mkw 0x081fe5b015806a00 0xe103fcb602b00d40 0x7ffffff01fc07f05 0xeffffffe03f80fe0

def z960 : W := mkw 0x0a02192503124824 0x21404324a0624904 0xa9a6b90c073040e6 0x7534d72180e6081c

def z961 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xffdffffff83c7006 0xfffbffffff078e00

def z962 : W := mkw 0xe40af5ff48281050 0xfc815ebfe905020a 0xf840ffffe03c70fe 0x1f081ffffc078e1f

def z963 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xff9ffffff83c40e6 0xfff3ffffff07881c

def z964 : W := mkw 0xca0211ffc100cca4 0x3940423ff8201994 0xa00001ed80004ce4 0x1400003db000099c

def z965 : W := mkw 0x00352c0016920000 0x4006a58002d24000 0x0026380007000000 0x0004c70000e00000

def z966 : W := mkw 0x01000000a000858a 0x00200000140010b1 0xeac04033e00c0f9e 0xbd5808067c0181f3

def z967 : W := mkw 0x0000080002120000 0x0000010000424000 0x1da6b80007038001 0x03b4d70000e07000

def z968 : W := mkw 0xca1ffdffd792eea4 0xf943ffbffaf25dd4 0xfffffffffff3ffe7 0xfffffffffffe7ffc

def z969 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbfffc01ffff003 0xe3f7fff803fffe00

def z970 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x4bd8c0c2183c301a 0xe97b181843078603

def z971 : W := mkw 0xee0ad1ffc928dcf4 0xbdc15a3ff9251b9e 0xebd8c1fff83c7cfe 0xfd7b183fff078f9f

def z972 : W := mkw 0x3028ee000a7f0000 0xc6051dc0014fe000 0x1fbefe001f3f8003 0xe3f7dfc003e7f000

def z973 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d86b80000000000 0x03b0d70000000000

def z974 : W := mkw 0x0a0000008100cca4 0x0140000010201994 0x0000000000004ce4 0x000000000000099c

def z975 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xffdfffffe03070fe 0x7ffbfffffc060e1f

def z976 : W := mkw 0x0000000080008480 0x0000000010001090 0xfec1003180c38f87 0xbfd82006301871f0

def z977 : W := mkw 0x0e0211258100dcf4 0x21c04224b0201b9e 0xa040012d80007cfc 0x14080025b0000f9f

def z978 : W := mkw 0xc01df44f40000000 0xd803be89e8000000 0xff9ffe3fe0000000 0x1ff3ffc7fc000000

def z979 : W := mkw 0x0000000080008480 0x0000000010001090 0x1400002180038c01 0x0280000430007180

def z980 : W := mkw 0xbf08ca4aab7fddfe 0x97e11949556ffbbf 0xebf8c1ce1fffffff 0xfd7f1839c3ffffff

def z981 : W := mkw 0x0000080002120000 0x0000010000424000 0x1fa7fe0007338003 0x63f4ffc000e67000

def z982 : W := mkw 0xbc3feffa1fff7a50 0xf787fdff43ffef4a 0xfffffffe1fffffff 0xffffffffc3ffffff

def z983 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1bbefe001f3f8002 0xe377dfc003e7f000

def z984 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x993effce1f3ff0fa 0x5327dff9c3e7fe1f

def z985 : W := mkw 0x13000a00a25785ae 0x02600140144af0b5 0x00000000003f80fa 0x000000000007f01f

def z986 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0427000007c00001 0x0084e00000f80000

def z987 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xe15881ce183c70fe 0xfc2b1039c3078e1f

def z988 : W := mkw 0x401735b554802200 0x6802e6b6aa900440 0x565f3ef1f8c03300 0x8acbe7de3f180660

def z989 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xffe7b93fe7f3cfff 0xfffcf727fcfe79ff

def z990 : W := mkw 0x0a0211b58100eea4 0x21404236b0201dd4 0xa000013d80004fe4 0x14000027b00009fc

def z991 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0x151fbe31e0000000 0x02a3f7c63c000000

def z992 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1fbfbe001ff38003 0xe3f7f7c003fe7000

def z993 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x7fffffc21ffff01f 0xeffffff843fffe03

def z994 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffffc00f01 0xfff7fffffff801e0

def z995 : W := mkw 0x4a173db5d792eea4 0x6942e7b6baf25dd4 0xffffbffdfff3ffe7 0xfffff7ffbffe7ffc

def z996 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd8c1fff83c70fe 0xfd7b183fff078e1f

def z997 : W := mkw 0x3a221b259fffcca4 0x27444364b3fff994 0xbda6b92d9fffcce7 0xf7b4d725b3fff99c

def z998 : W := mkw 0x3f000a00ab7fddfe 0x07e00140156ffbbf 0x006000001fffffff 0xe00c000003ffffff

def z999 : W := mkw 0x103dee0016d70000 0xc207bdc002dae000 0x1fbffe001fc38001 0xe3f7ffc003f87000

def z1000 : W := mkw 0xae0ad96f8b3adcf4 0xb5c15b2df1675b9e 0xbda6f92f873fccff 0x77b4df25f0e7f99f

def z1001 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1526b92d8733cce7 0x62a4d725b0e6799c

def z1002 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x42414633e0cc0f18 0x884828c67c1981e3

def z1003 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x17bfbe001ff38001 0xe2f7f7c003fe7000

def z1004 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z1005 : W := mkw 0x0802112501004800 0x21004224a0200900 0x35a6392187004c05 0x66b4c72430e00980

def z1006 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0xfffffe33ffff831b 0xffffffc67ffff063

def z1007 : W := mkw 0x0000080002120000 0x0000010000424000 0x7fe7b83007f38f07 0xeffcf70600fe71e0

def z1008 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9e81fe0fe0000000 0x13d03fc1fc000000

def z1009 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xfbfeffce1f3ff0fe 0xff7fdff9c3e7fe1f

def z1010 : W := mkw 0x0a02192503124824 0x21404324a0624904 0xbda6b92d8733c063 0x77b4d725b0e6780c

def z1011 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xe040012f80004cfc 0x1c080025f000099f

def z1012 : W := mkw 0x8e02196f8312dcf4 0x31c0432df0625b9e 0xfde6b9ef8733fcff 0x7fbcd73df0e67f9f

def z1013 : W := mkw 0xd03deeda56d70000 0xda07bddb4adae000 0x563f7ed267c38001 0x0ac7efda4cf87000

def z1014 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x8000010d800040e0 0x10000021b000081c

def z1015 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xeffec1ce1f3c70ff 0xfdffd839c3e78e1f

def z1016 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffc7fe33e0cf8f9f 0xbff8ffc67c19f1f3

def z1017 : W := mkw 0x0a0211b58100eea4 0x21404236b0201dd4 0x604001f180007f04 0x0c08003e30000fe0

def z1018 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffffc07001 0xfff7fffffff80e00

def z1019 : W := mkw 0x001701b000000000 0x2002e03600000000 0x011e01c000000000 0x0023c03800000000

def z1020 : W := mkw 0x31200a00beff858a 0x0624014017dff0b1 0x002000001fff8f03 0xe004000003fff1e0

def z1021 : W := mkw 0xb43de64a1ced1050 0xd687bcc9439da20a 0x021946c018cc3000 0x804328d803198600

def z1022 : W := mkw 0xc01ff5ff54802200 0xf803febfea900440 0xff9fffffe0c00300 0x1ff3fffffc180060

def z1023 : W := mkw 0x11352e0036d7010a 0x4226a5c006dae021 0x14273e1067c38301 0x0284e7c20cf87060

def z1024 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xfde6b92f8733ccff 0x7fbcd725f0e6799f

def z1025 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x66e7003007c00f05 0xacdce00600f801e0

def z1026 : W := mkw 0x0a1709b09792eea4 0x2142e13612f25dd4 0x67ff01f01ff3ffe7 0xecffe03e03fe7ffc

def z1027 : W := mkw 0x191703b0b5c5ef8a 0x2322e07616b8bdf1 0x67ff01f01fcfff9f 0xecffe03e03f9fff3

def z1028 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa800812d80304ce6 0x15001025b006099c

def z1029 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe03c40fe 0xfffbfffffc07881f

def z1030 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1da6b90c0733cce7 0x63b4d72180e6799c

def z1031 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x9ffffe0e1ffff0ff 0xf3ffffc1c3fffe1f

def z1032 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe7ff3fe7f3cfe7 0xfffcffe7fcfe79fc

def z1033 : W := mkw 0x191703b0b5c5ef8a 0x2322e07616b8bdf1 0x77ff07f1ffc3ff05 0xeeffe0fe3ff87fe0

def z1034 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9fffffe00c0018 0x1ff3fffffc018003

def z1035 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xa020012d8733cce7 0x74040025b0e6799c

def z1036 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x9c077e33e0000000 0x1380efc67c000000

def z1037 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x0126b90c0733cc61 0x4024d72180e6798c

def z1038 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0xda58fecff80c3018 0x9b4b1fd9ff018603

def z1039 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x779f7ff3e0000000 0x0ef3effe7c000000

def z1040 : W := mkw 0x02021925821284a4 0x20404324b0425094 0xbda6b92d873380e3 0x77b4d725b0e6701c

def z1041 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xf800fe3fe0000000 0x1f001fc7fc000000

def z1042 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe0cc0f9f 0xbffbfffffc1981f3

def z1043 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67ff01f01fc03f01 0x8cffe03e03f807e0

def z1044 : W := mkw 0xc00af56f40000000 0xf8015eade8000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z1045 : W := mkw 0x801de44a00000000 0xd003bc8940000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1046 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x0000012d80004c60 0x00000025b000098c

def z1047 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x9c27fe0e07ff80fb 0x1384ffc1c0fff01f

def z1048 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xffffff0e1fffc0ff 0xffffffe1c3fff81f

def z1049 : W := mkw 0xc00ad1ff40000000 0xb8015a3fe8000000 0xeb98c1ffe0000000 0x1d73183ffc000000

def z1050 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x14273e3007c38f01 0x0284e7c600f871e0

def z1051 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0x9b98fe0fe0000000 0x13731fc1fc000000

def z1052 : W := mkw 0x1b171bb5b7d7efae 0x2362e376b6fafdf5 0x14273e31e7c38f01 0x0284e7c63cf871e0

def z1053 : W := mkw 0x001701b014802200 0x2002e03602900440 0x67df01f018c03300 0x8cfbe03e03180660

def z1054 : W := mkw 0x3a2aff258b7fcca4 0xe7455fe4b16ff994 0xbda6ff2d873fcce7 0x77b4dfe5b0e7f99c

def z1055 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x77ff7ff3ffc07f05 0xeeffeffe7ff80fe0

def z1056 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x15a73e0007c38001 0x62b4e7c000f87000

def z1057 : W := mkw 0x0000080002120000 0x0000010000424000 0xffe6f802073f809f 0xfffcdf0040e7f013

def z1058 : W := mkw 0x34200a001eff1050 0x0684014003dfe20a 0x006000001ffff0ff 0xe00c000003fffe1f

def z1059 : W := mkw 0x30350a001eff0000 0x0606a14003dfe000 0x07bf00001fff8003 0xe0f7e00003fff000

def z1060 : W := mkw 0x481735b541006a00 0x6902e6b6a8200d40 0x14073e31e0000f00 0x0280e7c63c0001e0

def z1061 : W := mkw 0x0000100500000000 0x00000200a0000000 0x9800fe0fe0000000 0x13001fc1fc000000

def z1062 : W := mkw 0xe008f44f48280000 0xdc011e89e9050000 0x9b98fe0ff83c0002 0xf3731fc1ff078000

def z1063 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1dbeb8001fff8003 0xe3b7d70003fff000

def z1064 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xfc07ffffe0000000 0x1f80fffffc000000

def z1065 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffffb9fd9ff3ffe7 0xfffff73fb3fe7ffc

def z1066 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x153f3ff1ff007000 0x42a7e7fe3fe00e00

def z1067 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x25fe01e01fc07f05 0xe4bfc03c03f80fe0

def z1068 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfe814633e00f809a 0x1fd028c67c01f013

def z1069 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0x9818fecfe0000000 0x13031fd9fc000000

def z1070 : W := mkw 0x101dee0002570000 0xc203bdc0004ae000 0x1fbffe0007ff8003 0xe3f7ffc000fff000

def z1071 : W := mkw 0x0000000000000000 0x0000000000000000 0x76c10631e0c00f05 0xaed820c63c1801e0

def z1072 : W := mkw 0xc000344f40000000 0x58000689e8000000 0x90003e0fe0000000 0x120007c1fc000000

def z1073 : W := mkw 0x0015240000000000 0x4002a48000000000 0x14073e0000000000 0x0280e7c000000000

def z1074 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x9f9fffcfe0000000 0x13f3fff9fc000000

def z1075 : W := mkw 0x11200a00b6d7858a 0x0224014016daf0b1 0x0020000007c38f01 0x0004000000f871e0

def z1076 : W := mkw 0xb53dee4a3eff115a 0xd6a7bdc947dfe22b 0xffffffde7ffff3ff 0xfffffffbcffffe7f

def z1077 : W := mkw 0x240008000a3a1050 0x048001000147420a 0x1de6b8001f3ff0ff 0xe3bcd70003e7fe1f

def z1078 : W := mkw 0x01000000a000858a 0x00200000140010b1 0x00000031e0000f00 0x000000063c0001e0

def z1079 : W := mkw 0x01000000a000858a 0x00200000140010b1 0xe6c10033e0c00f9d 0xbcd820067c1801f3

def z1080 : W := mkw 0x0802012001004800 0x2100402400200900 0x2000012000004c04 0x0400002400000980

def z1081 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x07bf01f01fc07f01 0xe0f7e03e03f80fe0

def z1082 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffd9c7fff8ffffff 0xfffb38ffff1fffff

def z1083 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0xffffffce1ffff007 0xfffffff9c3fffe00

def z1084 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x66e100301fc07f05 0xecdc200603f80fe0

def z1085 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec14633f8cfff9f 0xffd828c67f19fff3

def z1086 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x153eb8001f338001 0x42a7d70003e67000

def z1087 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x3fbfff001fffc007 0xe7f7ffe003fff800

def z1088 : W := mkw 0x3b200a00bfffcdae 0x0764014017fff9b5 0x006000001fffcfff 0xe00c000003fff9ff

def z1089 : W := mkw 0x0015009014802200 0x0002a01202900440 0x47ff00d01fc03301 0xe8ffe01a03f80660

def z1090 : W := mkw 0x903dee4a16d70000 0xd207bdc942dae000 0xffbfffce07c38001 0x1ff7fff9c0f87000

def z1091 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x25bf01f01fc07f05 0x64b7e03e03f80fe0

def z1092 : W := mkw 0x00152c0002120000 0x4002a58000424000 0x14273e0007038001 0x0284e7c000e07000

def z1093 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa100812d80304ce4 0x54201025b006099c

def z1094 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x002638001fff8003 0xe004c70003fff000

def z1095 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800800c003000e2 0x110010018006001c

def z1096 : W := mkw 0x110002002045010a 0x022000400408a021 0xfec14633e0cc0318 0x9fd828c67c198063

def z1097 : W := mkw 0x0a0211b58100eea4 0x21404236b0201dd4 0xebd881fd98307fe6 0xfd7b103fb3060ffc

def z1098 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa880012d80004ce6 0x35100025b000099c

def z1099 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x14077e33e0000000 0x0280efc67c000000

def z1100 : W := mkw 0xac08c04a1da87a50 0x9581180943b50f4a 0xebf8c1ce1ffc7fff 0xfd7f1839c3ff8fff

def z1101 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec14633e0cf8f19 0x9fd828c67c19f1e3

def z1102 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x5ffffec21ffff0ff 0xebffffd843fffe1f

def z1103 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xf91effffe0000000 0x1f23dffffc000000

def z1104 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x477f01f01fc07f01 0xc8efe03e03f80fe0

def z1105 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xeac0412f800c4cfe 0xbd580825f001899f

def z1106 : W := mkw 0x0b021925a312cdae 0x21604324b46259b5 0xffe6f93fe73fcfff 0xfffcdf27fce7f9ff

def z1107 : W := mkw 0x4000340540000000 0x48000680a8000000 0xfe817e33e0000000 0x1fd02fc67c000000

def z1108 : W := mkw 0x001de40014800000 0xc003bc8002900000 0xfffffe33ffc00f05 0xffffffc67ff801e0

def z1109 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xbfbffe219fff8003 0xf7f7ffc433fff000

def z1110 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xffffffc21ffff09f 0xfffffff843fffe13

def z1111 : W := mkw 0x0000000000000000 0x0000000000000000 0xff87fe33e0000000 0x1ff0ffc67c000000

def z1112 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x17bf3e0007c38001 0x02f7e7c000f87000

def z1113 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbca6b82d87338ce7 0x3794d705b0e6719c

def z1114 : W := mkw 0x601ff5b548280000 0xec03feb6a9050000 0x1f9ffe31f83c0002 0xe3f3ffc63f078000

def z1115 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x657f01f01fc07f05 0x4cafe03e03f80fe0

def z1116 : W := mkw 0x0802092003124800 0x2100412400624900 0x3da6b9200733cc07 0x67b4d72400e67980

def z1117 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xbfbfff0e1fffc0ff 0xf7f7ffe1c3fff81f

def z1118 : W := mkw 0xf03deeda5eff2200 0xde07bddb4bdfe440 0x5ffffed27fffb303 0xebffffda4ffff660

def z1119 : W := mkw 0xc00211ff40000000 0x3800423fe8000000 0xff87ffffe0000000 0x1ff0fffffc000000

def z1120 : W := mkw 0x8400004a00001050 0x108000094000020a 0xeac041ce000c70fe 0xbd580839c0018e1f

def z1121 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfa414633e0cf8f9e 0x9f4828c67c19f1f3

def z1122 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x427800c01fc07f05 0xe84f001803f80fe0

def z1123 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xdffffece1fffb0fb 0xfbffffd9c3fff61f

def z1124 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xb800b92d8033cce6 0x17001725b006799c

def z1125 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0x7fffffc01ffff0ff 0xeffffff803fffe1f

def z1126 : W := mkw 0x0000080002120000 0x0000010000424000 0x3da6b82007338c07 0x67b4d70400e67180

def z1127 : W := mkw 0x1b000a00b7d7efae 0x0360014016fafdf5 0x006000001fffffff 0xe00c000003ffffff

def z1128 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x35873f31e0000000 0x06b0e7e63c000000

def z1129 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9926b90d8733cce7 0x7324d721b0e6799c

def z1130 : W := mkw 0x34352e001eff1050 0x4686a5c003dfe20a 0x14673e001ffff0ff 0xe28ce7c003fffe1f

def z1131 : W := mkw 0x0b0219b5a312efae 0x21604336b4625df5 0xfde6b9ffe733ffff 0x7fbcd73ffce67fff

def z1132 : W := mkw 0x4a173db5c312cca4 0x6942e7b6b8625994 0x14273e31e7038c01 0x0284e7c63ce07180

def z1133 : W := mkw 0xc00af5ff40000000 0xf8015ebfe8000000 0x9800ffcfe0000000 0x13001ff9fc000000

def z1134 : W := mkw 0x0a0018058312cca4 0x01400300b0625994 0x9820b80d8733cce7 0x73041701b0e6799c

def z1135 : W := mkw 0x343dee001eff1050 0xc687bdc003dfe20a 0x1ffffe001fffb01b 0xe3ffffc003fff603

def z1136 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xff9fffffe0004c04 0x1ff3fffffc000980

def z1137 : W := mkw 0x31200a00beff858a 0x0624014017dff0b1 0xfee14633ffff8f9f 0xffdc28c67ffff1f3

def z1138 : W := mkw 0xb408ca4a0a7f1050 0x96811949414fe20a 0xffffffce1ffff0ff 0xfffffff9c3fffe1f

def z1139 : W := mkw 0xe41de4da48281050 0xdc83bc9b4905020a 0x425946d2780c3018 0x884b28da4f018603

def z1140 : W := mkw 0x0000000000000000 0x0000000000000000 0x425800c018003000 0x884b001803000600

def z1141 : W := mkw 0x3a3fff251fff4824 0xe747ffe4a3ffe904 0x1fbfff0c1fffc063 0xe3f7ffe183fff80c

def z1142 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff8307064 0xfffbffffff060e0c

def z1143 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffbfffffffc07f01 0x5ff7fffffff80fe0

def z1144 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffd947f3e0cf8f9f 0xbffb28fe7c19f1f3

def z1145 : W := mkw 0x50352e9056d70000 0x4a06a5d20adae000 0x14273e1067c38001 0x0284e7c20cf87000

def z1146 : W := mkw 0x203dec001eba0000 0xc407bd8003d74000 0x1fbef8001f3f8003 0xe3f7df0003e7f000

def z1147 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xbc80012d8003cce7 0x37900025b000799c

def z1148 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x6fff41f01fcc7f07 0xedffe83e03f98fe0

def z1149 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0304060 0x5ff3fffffc06080c

def z1150 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x567f7ef3ffc03f01 0x8acfefde7ff807e0

def z1151 : W := mkw 0xb708da4faa7f95fe 0x96e11b49f54ff2bf 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z1152 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda6f92f873fccff 0x77b4df25f0e7f99f

def z1153 : W := mkw 0x3228fe058a7f84a4 0xc6451fc0b14ff094 0x9800fe0d803f80e2 0x13001fc1b007f01c

def z1154 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xca58c0ce183c30fa 0x994b1819c307861f

def z1155 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbfa7b92d87f3cce7 0xf7f4f725b0fe799c

def z1156 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1fbf7e001fcf8003 0xe3f7efc003f9f000

def z1157 : W := mkw 0x0a0211b58100eea4 0x21404236b0201dd4 0x0000003180000f00 0x00000006300001e0

def z1158 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x17bf3e001fff8003 0xe2f7e7c003fff000

def z1159 : W := mkw 0xae0ad1ff8928fef4 0xb5c15a3ff1251fde 0xebd8c1ff983c7ffe 0xfd7b183ff3078fff

def z1160 : W := mkw 0x0000080002120000 0x0000010000424000 0x1ca6380007038003 0x2394c70000e07000

def z1161 : W := mkw 0x323dfe059eff84a4 0xc647bfc0b3dff094 0x9fbffe0d9fff80e3 0xf3f7ffc1b3fff01c

def z1162 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x7fffffcc1ffff067 0xeffffff983fffe0c

def z1163 : W := mkw 0x0a0008008312cca4 0x0140010010625994 0x1da6b8000733cce7 0x63b4d70000e6799c

def z1164 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xe6c1013d80c04fe5 0xbcd82027b01809fc

def z1165 : W := mkw 0xf03deeda5eff0000 0xde07bddb4bdfe000 0x1fbffec01fff8003 0xe3f7ffd803fff000

def z1166 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x56414633e0cf8f9f 0xaac828c67c19f1f3

def z1167 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x07bf01c01fc07001 0xe0f7e03803f80e00

def z1168 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbde6b92d873fccff 0xf7bcd725b0e7f99f

def z1169 : W := mkw 0x0015009014802200 0x0002a01202900440 0x66d900f018c03f05 0xacdb201e031807e0

def z1170 : W := mkw 0xd108f64fe045858a 0xda211ec9fc08b0b1 0x9800fe0fe00f809a 0x13001fc1fc01f013

def z1171 : W := mkw 0x0a1ffd258312cca4 0xe143ffa4b0625994 0xbfbfff2d8733cce7 0x77f7ffe5b0e6799c

def z1172 : W := mkw 0xc008e44a40000000 0xd8011c8948000000 0x0000460260000000 0x000008c04c000000

def z1173 : W := mkw 0xc01df44f54800000 0xd803be89ea900000 0x9fbffe0fffc00001 0xf3f7ffc1fff80000

def z1174 : W := mkw 0xe01ff5ff48280000 0xfc03febfe9050000 0xff9fffffe03c0002 0x1ff3fffffc078000

def z1175 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd9c7de783c70fe 0xfd7b38fbcf078e1f

def z1176 : W := mkw 0xc000104f40000000 0x18000209e8000000 0x8000000fe0000000 0x10000001fc000000

def z1177 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffe7c07f05 0x1ffffffffcf80fe0

def z1178 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x07ff01c01fc07f05 0xe0ffe03803f80fe0

def z1179 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1da7be0007c38001 0x03b4f7c000f87000

def z1180 : W := mkw 0x10150a0016d70000 0x0202a14002dae000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z1181 : W := mkw 0x13000a00a25785ae 0x02600140144af0b5 0x0040000000ff8fff 0xa0080000001ff1ff

def z1182 : W := mkw 0x1b000a00a357cdae 0x03600140146af9b5 0x00200000073fccff 0x6004000000e7f99f

def z1183 : W := mkw 0x0a0219b58312eea4 0x21404336b0625dd4 0xfffeb9fd9f33ffe7 0xffffd73fb3e67ffc

def z1184 : W := mkw 0x0015080016920000 0x0002a10002d24000 0x1da7b80007f38003 0x63b4f70000fe7000

def z1185 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xf800ffcfe0000000 0x1f001ff9fc000000

def z1186 : W := mkw 0xb528ca4abeff95da 0x96a5194957dff2bb 0xebf8c1ce1fffffff 0xfd7f1839c3ffffff

def z1187 : W := mkw 0x2e0211258928dcf4 0x25c04224b1251b9e 0xa040012d983c7cfe 0xf4080025b3078f9f

def z1188 : W := mkw 0x3028ca000a7f0000 0x86051940014fe000 0x0800c000003f8002 0x010018000007f000

def z1189 : W := mkw 0xcc1ff5ff41007a50 0xf983febfe8200f4a 0xffdfffffe0007ffc 0x1ffbfffffc000fff

def z1190 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xb426392d8703cce5 0x1684c725b0e0799c

def z1191 : W := mkw 0x313dee00beff858a 0xc627bdc017dff0b1 0x1ffffe001fff8f9f 0xe3ffffc003fff1f3

def z1192 : W := mkw 0xd03fffff56d70000 0xfa07ffffeadae000 0xffbfffffe7c38001 0x1ff7fffffcf87000

def z1193 : W := mkw 0x0a1719b59792eea4 0x2142e336b2f25dd4 0x1427383187c38f01 0x0284e70630f871e0

def z1194 : W := mkw 0xe81ff5ff5da86a00 0xfd03febfebb50d40 0xfffffffffffc7f07 0xffffffffffff8fe0

def z1195 : W := mkw 0x0000080002120000 0x0000010000424000 0x0020000007338003 0x6004000000e67000

def z1196 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9826b80d873380e2 0x1304d701b0e6701c

def z1197 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xff99ffffe0000000 0x1ff33ffffc000000

def z1198 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x14273e31e7c38001 0x0284e7c63cf87000

def z1199 : W := mkw 0x1000020000450000 0x020000400008a000 0x1401060000c38001 0x028020c000187000

def z1200 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xbd9fbffde0000000 0x17b3f7ffbc000000

def z1201 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xffbfffce1fff80fb 0xfff7fff9c3fff01f

def z1202 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1203 : W := mkw 0x480211b541006a00 0x29004236a8200d40 0x604001f1e0007f04 0x0c08003e3c000fe0

def z1204 : W := mkw 0xec1ff5ff49287a50 0xfd83febfe9250f4a 0xffdffffff83c7ffe 0xfffbffffff078fff

def z1205 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xa998c1ce183c70fe 0x75331839c3078e1f

def z1206 : W := mkw 0x1b021b25a357cdae 0x23604364b46af9b5 0xbda6ff2fe73fccff 0x77b4dfe5fce7f99f

def z1207 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x1426b82d87338c61 0x0284d705b0e6718c

def z1208 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0x9800fe0fe00c0018 0x13001fc1fc018003

def z1209 : W := mkw 0x0008ec0002120000 0xc0011d8000424000 0x1da6fe0007338003 0x63b4dfc000e67000

def z1210 : W := mkw 0x001711b500000000 0x2002e236a0000000 0xff9fb9fd80000000 0x1ff3f73fb0000000

def z1211 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x16277e0007cf8001 0x82c4efc000f9f000

def z1212 : W := mkw 0x0000000000000000 0x0000000000000000 0x0980800000300002 0x6130100000060000

def z1213 : W := mkw 0xc01df44f40000000 0xd803be89e8000000 0x991efe0fe0000000 0x1323dfc1fc000000

def z1214 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xfbdeffcff83c70fe 0xff7bdff9ff078e1f

def z1215 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x151f3ff1e0000000 0x02a3e7fe3c000000

def z1216 : W := mkw 0x0802012015806a00 0x2100402402b00d40 0x25e601201fc07f05 0xe4bcc02403f80fe0

def z1217 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0xffffffce1fff809f 0xfffffff9c3fff013

def z1218 : W := mkw 0xe03ff5ff5ca80000 0xfc07febfeb950000 0xff9ffffff8000000 0x1ff3ffffff000000

def z1219 : W := mkw 0x31200a00aa7f858a 0x06240140154ff0b1 0x00000000003f809a 0x000000000007f013

def z1220 : W := mkw 0x0015080016920000 0x0002a10002d24000 0xffffb9cc1ff3f0e7 0xfffff73983fe7e1c

def z1221 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x9e814633e0cf8f9b 0xb3d028c67c19f1f3

def z1222 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x9fbffe021fff809b 0xf3f7ffc043fff013

def z1223 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0x5fffffce1ffff07b 0xebfffff9c3fffe0f

def z1224 : W := mkw 0x39370bb0bfffef8a 0x2726e17617fffdf1 0x67ff01f01fffff9f 0xecffe03e03fffff3

def z1225 : W := mkw 0x4002352540000000 0x680046a4a8000000 0x14063e21e0000000 0x0280c7c43c000000

def z1226 : W := mkw 0xa608d84f8a3a94f4 0x94c11b09f147529e 0x9800f80f803f80fa 0x13001f01f007f01f

def z1227 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0xfbd8c7cff83ff0fe 0xff7b18f9ff07fe1f

def z1228 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xffffffcc1ffff0e7 0xfffffff983fffe1c

def z1229 : W := mkw 0xc208fc4fc21284a4 0xd8411f89f8425094 0x9800fe0fe03380e2 0x13001fc1fc06701c

def z1230 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0x1800fe0000000000 0x03001fc000000000

def z1231 : W := mkw 0xf03dfe4f5eff0000 0xde07bfc9ebdfe000 0x9fbffe0fffff8003 0xf3f7ffc1fffff000

def z1232 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffdffffff8c07f04 0x9ffbffffff180fe0

def z1233 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x779fbffde0000000 0x0ef3f7ffbc000000

def z1234 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa000012d80000c00 0x14000025b0000180

def z1235 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z1236 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xe7ff01fc1fc07fe5 0xfcffe03f83f80ffc

def z1237 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x0000800c00300060 0x000010018006000c

def z1238 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0300002 0x7ff3fffffc060000

def z1239 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa5a6012d87004ce5 0x74b4c025b0e0099c

def z1240 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xffffffffe7c04f05 0xfffffffffcf809e0

def z1241 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x0000000000c38f01 0x00000000001871e0

def z1242 : W := mkw 0x2400000008281050 0x048000000105020a 0xeac04002183c70fe 0xfd58080043078e1f

def z1243 : W := mkw 0xca0211ffc100cca4 0x3940423ff8201994 0xe00001ffe0000c00 0x1c00003ffc000180

def z1244 : W := mkw 0x200008000a3a0000 0x0400010001474000 0x1da6b8001f3f8003 0xe3b4d70003e7f000

def z1245 : W := mkw 0x2400000008281050 0x048000000105020a 0x00000000003c00fa 0x000000000007801f

def z1246 : W := mkw 0x783fffb55fff6a00 0xef07fff6abffed40 0x7ffffff1ffffff07 0xeffffffe3fffffe0

def z1247 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x77ffbffdffc07f05 0xeefff7ffbff80fe0

def z1248 : W := mkw 0x31200a00beff858a 0x0624014017dff0b1 0x002000001fff809b 0xe004000003fff013

def z1249 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x163f7e001fff8003 0xe2c7efc003fff000

def z1250 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0xffbfffce1fffc0e7 0xfff7fff9c3fff81c

def z1251 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x993effcfff007000 0x5327dff9ffe00e00

def z1252 : W := mkw 0x0000080002120000 0x0000010000424000 0x3da6b9000733c007 0x67b4d72000e67800

def z1253 : W := mkw 0x0802112501004800 0x21004224a0200900 0xffe7ff3fe7c04f05 0xfffcffe7fcf809e0

def z1254 : W := mkw 0x0a0211258100eea4 0x21404224b0201dd4 0xa040012d80007fe4 0x14080025b0000ffc

def z1255 : W := mkw 0x0002112500000000 0x20004224a0000000 0xffc7ff3fe03c40fe 0xfff8ffe7fc07881f

def z1256 : W := mkw 0x0015089016922200 0x0002a11202d24440 0x5fffb8d01ff3b303 0xebfff71a03fe7660

def z1257 : W := mkw 0xc01ff5ff54802200 0xf803febfea900440 0xffffffffffc03301 0xfffffffffff80660

def z1258 : W := mkw 0xc41735ff40001050 0x7882e6bfe800020a 0xf4473fffe00070fc 0x1e88e7fffc000e1f

def z1259 : W := mkw 0x201dc8001eba0000 0x8403b90003d74000 0x1fbff8001fff8003 0xe3f7ff0003fff000

def z1260 : W := mkw 0x0a1719b58312cca4 0x2142e336b0625994 0xffbfb9fd8733cce7 0x7ff7f73fb0e6799c

def z1261 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x77df3ff1f8007004 0xeefbe7fe3f000e00

def z1262 : W := mkw 0xc01ffdff42120000 0xf803ffbfe8424000 0xffbfffffe733c0e7 0x7ff7fffffce6781c

def z1263 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xebd9c1de18fc73fe 0xfd7b383bc31f8e7f

def z1264 : W := mkw 0x10352e9016d72200 0x4206a5d202dae440 0x567f3ed01fc3b301 0x8acfe7da03f87660

def z1265 : W := mkw 0x401df40540000000 0xc803be80a8000000 0x1f9ffe01e0000000 0x03f3ffc03c000000

def z1266 : W := mkw 0x881fc1fa15806a00 0xb103f83f42b00d40 0xefffc1fe1fc07f05 0xfdfff83fc3f80fe0

def z1267 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0xfea77e33e7c38001 0x1fd4efc67cf87000

def z1268 : W := mkw 0x0800000015806a00 0x0100000002b00d40 0x0020000007c00f01 0x0004000000f801e0

def z1269 : W := mkw 0xc00af56f40000000 0xf8015eade8000000 0x9906ff0fe0000000 0x1320dfe1fc000000

def z1270 : W := mkw 0xc41ff5ff40001050 0xf883febfe800020a 0xff9fffffe0007060 0x1ff3fffffc000e0c

def z1271 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe0000004 0xbffbfffffc000000

def z1272 : W := mkw 0x0a02192503124824 0x21404324a0624904 0x1526b90c0733c061 0x42a4d72180e6780c

def z1273 : W := mkw 0x0000080082128480 0x0000010010425090 0xbda6b92d8733cce7 0x77b4d725b0e6799c

def z1274 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0x00000031e0000f00 0x000000063c0001e0

def z1275 : W := mkw 0xa43dec4a1eba1050 0xd487bd8943d7420a 0xebfef9ce1f3c70fe 0xfd7fdf39c3e78e1f

def z1276 : W := mkw 0x0a0219b58312eea4 0x21404336b0625dd4 0xbda6b9ed8733fce7 0x77b4d73db0e67f9c

def z1277 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0x1fbfffcc1fff8003 0xe3f7fff983fff000

def z1278 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffd9c7ce183c70fe 0xfffb38f9c3078e1f

def z1279 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffc1c73fe0cf8f9f 0xbff838e7fc19f1f3

def z1280 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9ffffff83c7062 0xfff3ffffff078e0c

def z1281 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9fffffe03c40fe 0x7ff3fffffc07881f

def z1282 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff80c701c 0xfffbffffff018e03

def z1283 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7fbfffc01fff8003 0xeff7fff803fff000

def z1284 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0xfffffe33ffff8f07 0xffffffc67ffff1e0

def z1285 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xbc80fe2fe0000000 0x17901fc5fc000000

def z1286 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xfac0fe0fe00c009e 0xbf581fc1fc018013

def z1287 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x66c1003000cf8f9f 0xacd820060019f1f3

def z1288 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x1407be3de0000000 0x0280f7c7bc000000

def z1289 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0x7ffffe327fff8f1f 0xefffffc64ffff1e3

def z1290 : W := mkw 0x481ff5b555806a00 0xe903feb6aab00d40 0x1fbffe31ffc00f01 0xe3f7ffc63ff801e0

def z1291 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0x161f7e31e0000000 0x02c3efc63c000000

def z1292 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0xfb99ffdfe0000000 0x1f733ffbfc000000

def z1293 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0x1fbffe107fff8303 0xe3f7ffc20ffff060

def z1294 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xb526b92d8733cce5 0x56a4d725b0e6799c

def z1295 : W := mkw 0x4000340540000000 0x48000680a8000000 0x98007e03e0000000 0x13000fc07c000000

def z1296 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x9c26b82d8733cce7 0x7384d705b0e6799c

def z1297 : W := mkw 0x2c1701b01da87a50 0x2582e03603b50f4a 0x67ff01f01ffc7fff 0xecffe03e03ff8fff

def z1298 : W := mkw 0xc81ff5ff55804800 0xf903febfeab00900 0xffbfffffffc04c05 0xfff7fffffff80980

def z1299 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0x0000002180004ce4 0x000000043000099c

def z1300 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xeb98c1ce183c70fa 0x5d731839c3078e1f

def z1301 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffa7b93d8733cce7 0x7ff4f727b0e6799c

def z1302 : W := mkw 0xb53dee4a3eff115a 0xd6a7bdc947dfe22b 0x5ffffed27fffb31b 0xebffffda4ffff663

def z1303 : W := mkw 0xf43deeda5eff1050 0xde87bddb4bdfe20a 0xffffffde7ffff0ff 0xfffffffbcffffe1f

def z1304 : W := mkw 0xc01df4df54802200 0xd803be9bea900440 0xda59fedff8c03300 0x9b4b3fdbff180660

def z1305 : W := mkw 0x202008001eba0000 0x0404010003d74000 0x1da6b8001f338003 0x63b4d70003e67000

def z1306 : W := mkw 0x001701b000000000 0x2002e03600000000 0x0407003000000000 0x0080e00600000000

def z1307 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x0b98c1cc183c7062 0xe173183983078e0c

def z1308 : W := mkw 0x481735b541006a00 0x6902e6b6a8200d40 0x74473ff1e0007f04 0x0e88e7fe3c000fe0

def z1309 : W := mkw 0x0008c80002120000 0x8001190000424000 0x1fbef80007338003 0x63f7df0000e67000

def z1310 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdfffffe0c00300 0x9ffbfffffc180060

def z1311 : W := mkw 0x10000a0002570000 0x02000140004ae000 0x14273e0007c38001 0x0284e7c000f87000

def z1312 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x14073e31e0c00f01 0x0280e7c63c1801e0

def z1313 : W := mkw 0xb43dee4a1eff1050 0xd687bdc943dfe20a 0xbfbfffcc1ffff0e7 0xf7f7fff983fffe1c

def z1314 : W := mkw 0x081701b001004800 0x2102e03600200900 0x67bf01f007004c05 0x6cf7e03e00e00980

def z1315 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xbd86b92d80004ce4 0x17b0d725b000099c

def z1316 : W := mkw 0x0200180502120024 0x00400300a0424004 0x0000b80c00300060 0x000017018006000c

def z1317 : W := mkw 0xf028fe4f4a7f0000 0xde051fc9e94fe000 0x9800fe0fe03f8002 0x13001fc1fc07f000

def z1318 : W := mkw 0x1b170bb0b7d7efae 0x2362e17616fafdf5 0x67ff01f01fffffff 0xecffe03e03ffffff

def z1319 : W := mkw 0x02001805821284a4 0x00400300b0425094 0xbc80b82d80338ce7 0x37901705b006719c

def z1320 : W := mkw 0x1115029034c5230a 0x0222a0520698a461 0x425946d278cc3318 0x884b28da4f198663

def z1321 : W := mkw 0xcb0211ffe100cdae 0x3960423ffc2019b5 0xe04001ffe0004ffc 0x1c08003ffc0009ff

def z1322 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0004004 0x7ff3fffffc000800

def z1323 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfe814633e0cf8f9b 0x1fd028c67c19f1f3

def z1324 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff83070fc 0x5ffbffffff060e1f

def z1325 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x013eb9cc1f007000 0x4027d73983e00e00

def z1326 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9ffffff83c00fa 0xfff3ffffff07801f

def z1327 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0xebd8c1ce18ffffff 0xfd7b1839c31fffff

def z1328 : W := mkw 0x0a0018058312cca4 0x01400300b0625994 0x9da6b80d8733cce7 0x73b4d701b0e6799c

def z1329 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xeb98c1ce18307060 0x5d731839c3060e0c

def z1330 : W := mkw 0x400235b540000000 0x680046b6a8000000 0x10003e31e0000000 0x020007c63c000000

def z1331 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1ffffe001fff809f 0xe3ffffc003fff013

def z1332 : W := mkw 0x10000a0002570000 0x02000140004ae000 0x1da7be0007f38003 0x63b4f7c000fe7000

def z1333 : W := mkw 0x081fe5b015806a00 0xe103fcb602b00d40 0xfffffff3ffc07f05 0xfffffffe7ff80fe0

def z1334 : W := mkw 0xe008f44f48280000 0xdc011e89e9050000 0x9800fe0fe03c0002 0x13001fc1fc078000

def z1335 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xff9fffffe0300060 0x1ff3fffffc06000c

def z1336 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xbd9effefe0000000 0x17b3dffdfc000000

def z1337 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa000002180000c84 0x1400000430000190

def z1338 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x1e877e31e0000000 0x03d0efc63c000000

def z1339 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67bf01f01fc07f01 0x4cf7e03e03f80fe0

def z1340 : W := mkw 0x30352e001eff0000 0x4606a5c003dfe000 0x14273e001ff38001 0x4284e7c003fe7000

def z1341 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x00000000000f809a 0x000000000001f013

def z1342 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0x56077e33e0000000 0x0ac0efc67c000000

def z1343 : W := mkw 0x4002352540000000 0x680046a4a8000000 0xbd86bf2de0000000 0x17b0d7e5bc000000

def z1344 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xffbfffffe7004000 0x5ff7fffffce00800

def z1345 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x14277e0007cf8001 0x0284efc000f9f000

def z1346 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0xffffffffff3c70fe 0xffffffffffe78e1f

def z1347 : W := mkw 0xc01df4df40000000 0xd803be9be8000000 0x9801fe1fe0000000 0x13003fc3fc000000

def z1348 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x9fbffe0c1fff80e3 0xf3f7ffc183fff01c

def z1349 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x14273e0007cf8003 0xa284e7c000f9f000

def z1350 : W := mkw 0x0000100500000000 0x00000200a0000000 0xfe81fe3fe0000000 0x1fd03fc7fc000000

def z1351 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffd94633f8cf8f9f 0xfffb28c67f19f1f3

def z1352 : W := mkw 0x0000080002120000 0x0000010000424000 0x0126b90c07304060 0x4024d72180e6080c

def z1353 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xfda6b93fe733cce7 0x7fb4d727fce6799c

def z1354 : W := mkw 0xc81ff5ff41006a00 0xf903febfe8200d40 0xffdfffffe0c07f05 0xbffbfffffc180fe0

def z1355 : W := mkw 0xb43deeda1eff3250 0xd687bddb43dfe64a 0xffffffde1ffff3ff 0xfffffffbc3fffe7f

def z1356 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xbda6b92d87338ce3 0x17b4d725b0e6719c

def z1357 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff8fc7fff 0xfffbffffff1f8fff

def z1358 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0xfffffffffff07f65 0xfffffffffffe0fec

def z1359 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1fbffe001fcf8001 0x83f7ffc003f9f000

def z1360 : W := mkw 0x0000000000000000 0x0000000000000000 0x25a6010007004005 0x64b4c02000e00800

def z1361 : W := mkw 0xb03dee4a1eff0000 0xd607bdc943dfe000 0xffbfffffffff8003 0xfff7fffffffff000

def z1362 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfac04603e00f809e 0xbf5808c07c01f013

def z1363 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x67bf01f01f007000 0x4cf7e03e03e00e00

def z1364 : W := mkw 0x111703b0a045858a 0x2222e0761408b0b1 0xffdf47f3e0cf8f9f 0xbffbe8fe7c19f1f3

def z1365 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x14673e31ffc07f05 0xe28ce7c63ff80fe0

def z1366 : W := mkw 0x0000000000000000 0x0000000000000000 0x98004603e0000000 0x130008c07c000000

def z1367 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b80007338087 0x77b4d70000e67010

def z1368 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0x151fbffdf8307060 0x42a3f7ffbf060e0c

def z1369 : W := mkw 0x0000000080008480 0x0000000010001090 0xfec04023800f8c9f 0xbfd808047001f193

def z1370 : W := mkw 0x10352e0016d70000 0x4206a5c002dae000 0x16a73e0007c38001 0xa2d4e7c000f87000

def z1371 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x1f9ffe31e0000000 0x03f3ffc63c000000

def z1372 : W := mkw 0x0a0211258100cca4 0x21404224b0201994 0xa980812d80004ce4 0x15301025b000099c

def z1373 : W := mkw 0xc01ff5ff54800000 0xf803febfea900000 0xff9ffffff8c00000 0x9ff3ffffff180000

def z1374 : W := mkw 0x11000a002257010a 0x02200140044ae021 0x5fe7fe1267ff831b 0xebfcffc24cfff063

def z1375 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe7f93f87ffcfff 0xfffcff27f0fff9ff

def z1376 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x1dbefe001f3f8003 0x63b7dfc003e7f000

def z1377 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfec14633e0ffcfff 0xffd828c67c1ff9ff

def z1378 : W := mkw 0xe41ff5ff5ca83250 0xfc83febfeb95064a 0xffdffffff8fc73fe 0xfffbffffff1f8e7f

def z1379 : W := mkw 0x8e0211ff8100fef4 0x31c0423ff0201fde 0xe04001ff80007ffc 0x1c08003ff0000fff

def z1380 : W := mkw 0x30200a001eff0000 0x0604014003dfe000 0x142638001fff8003 0xe284c70003fff000

def z1381 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x0bd8c1cc183c70fe 0xe17b183983078e1f

def z1382 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x3fbffe201fff8c07 0xe7f7ffc403fff180

def z1383 : W := mkw 0x10000a0002570000 0x02000140004ae000 0x1da6fe00073f8003 0x63b4dfc000e7f000

def z1384 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x113ebe001f338000 0x4227d7c003e67000

def z1385 : W := mkw 0xca1ff5ffc100cca4 0xf943febff8201994 0xe21947ffe0004ce4 0x1c4328fffc00099c

def z1386 : W := mkw 0xc01735ff40000000 0x7802e6bfe8000000 0xfd87bfffe0000000 0x1fb0f7fffc000000

def z1387 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xffbfffffe7304ce7 0x7ff7fffffce6099c

def z1388 : W := mkw 0xc81ff5ff41004800 0xf903febfe8200900 0xffffffffff007c05 0xffffffffffe00f80

def z1389 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0x9800c60fe03f80fa 0x130018c1fc07f01f

def z1390 : W := mkw 0xd91ff7fff5c5ef8a 0xfb23fefffeb8bdf1 0xffffffffffcfff9f 0xfffffffffff9fff3

def z1391 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffffffffff007004 0xffffffffffe00e00

def z1392 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xf6414633e0cf8f9d 0x9ec828c67c19f1f3

def z1393 : W := mkw 0xc008f4df40000000 0xd8011e9be8000000 0xd800fedfe0000000 0x1b001fdbfc000000

def z1394 : W := mkw 0x4000340540000000 0x48000680a8000000 0x9800be0de0000000 0x130017c1bc000000

def z1395 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdffffff80c709e 0xfffbffffff018e13

def z1396 : W := mkw 0xc81711ff55806a00 0x3902e23feab00d40 0xe7ff01ffffc07f05 0xfcffe03ffff80fe0

def z1397 : W := mkw 0x2008c8000a3a0000 0x8401190001474000 0x1dbeb8001f338003 0x63b7d70003e67000

def z1398 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0xfec1c63fe0ff8fff 0xbfd838c7fc1ff1ff

def z1399 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xfbd8ffcff8007004 0xff7b1ff9ff000e00

def z1400 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xbd87bf3de03040e6 0x77b0f7e7bc06081c

def z1401 : W := mkw 0xb508c24a286d115a 0x96a11849450da22b 0xebd9c7de78fc73fe 0xfd7b38fbcf1f8e7f

def z1402 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffdffffff8c07f05 0xfffbffffff180fe0

def z1403 : W := mkw 0x8e02116f8100dcf4 0x31c0422df0201b9e 0xa00001ed80007ce4 0x1400003db0000f9c

def z1404 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xfed946f3f8cfbf9f 0xbfdb28de7f19f7f3

def z1405 : W := mkw 0x0002112500000000 0x20004224a0000000 0xbd87bf3de0000000 0x17b0f7e7bc000000

def z1406 : W := mkw 0xa408c04a08281050 0x948118094105020a 0x8b98c1ce183c70fa 0xf1731839c3078e1f

def z1407 : W := mkw 0x0a1719b59792eea4 0x2142e336b2f25dd4 0x77ff39f19fc3ff05 0xeeffe73e33f87fe0

def z1408 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xbc873e31e0000000 0x1790e7c63c000000

def z1409 : W := mkw 0xe41ff5ff48281050 0xfc83febfe905020a 0xffdffffff83c30fa 0x9ffbffffff07861f

def z1410 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe00c0002 0xbff3fffffc018000

def z1411 : W := mkw 0xc80af5ff41006a00 0xf9015ebfe8200d40 0xf840ffffe0007f04 0x1f081ffffc000fe0

def z1412 : W := mkw 0x401735b540000000 0x6802e6b6a8000000 0xf4073e33e0000000 0x1e80e7c67c000000

def z1413 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xefff41f21fc07f05 0xfdffe83e43f80fe0

def z1414 : W := mkw 0x401ff5b540000000 0xe803feb6a8000000 0xbf9fff3de0000000 0x17f3ffe7bc000000

def z1415 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x617e01f01f007f04 0x4c2fc03e03e00fe0

def z1416 : W := mkw 0x0b021125a100cdae 0x21604224b42019b5 0xa040012d80004ffc 0x14080025b00009ff

def z1417 : W := mkw 0xe408f44f48281050 0xdc811e89e905020a 0x9840fe0ff83c70fe 0xf3081fc1ff078e1f

def z1418 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xde1ffeffe0000000 0x1bc3ffdffc000000

def z1419 : W := mkw 0x0000080002120000 0x0000010000424000 0x1800b80000338002 0x0300170000067000

def z1420 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x437f01d01fc07300 0xc86fe03a03f80e60

def z1421 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xeb98c1ce003040e6 0x7d731839c006081c

def z1422 : W := mkw 0x313dee003eff010a 0xc627bdc007dfe021 0xfffffe127fff839f 0xffffffc24ffff073

def z1423 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xe7ff01f21fc07f9d 0xfcffe03e43f80ff3

def z1424 : W := mkw 0x8a02116f8100cca4 0x3140422df0201994 0xe00001ef80004ce4 0x1c00003df000099c

def z1425 : W := mkw 0x1b021b25a357cdae 0x23604364b46af9b5 0xbde6b92d87ffcfff 0xf7bcd725b0fff9ff

def z1426 : W := mkw 0x3028ca000a7f0000 0x86051940014fe000 0x1da6f800073f8003 0x63b4df0000e7f000

def z1427 : W := mkw 0xf0351a4f5eff0000 0x1e06a349ebdfe000 0x87bf000fffff8003 0xf0f7e001fffff000

def z1428 : W := mkw 0x081725b015806a00 0x6102e4b602b00d40 0xffff7ff3ffc07f05 0xffffeffe7ff80fe0

def z1429 : W := mkw 0x0000080002120000 0x0000010000424000 0x1da6b90c0733c0e7 0x63b4d72180e6781c

def z1430 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x7fffbff1ffc07f05 0xeffff7fe3ff80fe0

def z1431 : W := mkw 0x4000340540000000 0x48000680a8000000 0x73983fc1e0000000 0x0e7307f83c000000

def z1432 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xffff7ff3ffcc7f9f 0xffffeffe7ff98ff3

def z1433 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b92d8733c0e7 0x77b4d725b0e6781c

def z1434 : W := mkw 0xa408e44a08281050 0xd4811c894105020a 0xffd9fffff83c70fe 0xfffb3fffff078e1f

def z1435 : W := mkw 0xc008f44f40000000 0xd8011e89e8000000 0xbd86ff0fe0000000 0x17b0dfe1fc000000

def z1436 : W := mkw 0x0000080002120000 0x0000010000424000 0x9926b90c0733c0e2 0x5324d72180e6781c

def z1437 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0xffdffffff8c03f00 0x9ffbffffff1807e0

def z1438 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xf7ff3ff3ffc07f05 0xfeffe7fe7ff80fe0

def z1439 : W := mkw 0xa408c84a0a3a1050 0x948119094147420a 0x567e78c21f0fb019 0x8acfcf1843e1f603

def z1440 : W := mkw 0x70221bb55eff0000 0x2e044376abdfe000 0x00200031ffff8003 0xe00400063ffff000

def z1441 : W := mkw 0x18222fb003576a00 0x630445f6006aed40 0x73d83ff01803ff04 0xee7b07fe03007fe0

def z1442 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0x9c27fe3fe7fc0ffb 0x1384ffc7fcff81ff

def z1443 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xffff01f01fc3ff87 0xffffe03e03f87ff0

def z1444 : W := mkw 0x1b0213252145492e 0x23604264a428a925 0x5ec1471e60cfc37b 0xabd828e3cc19f86f

def z1445 : W := mkw 0xc80af56f55806a00 0xf9015eadeab00d40 0xbde6ff2fffc07f05 0xf7bcdfe5fff80fe0

def z1446 : W := mkw 0x0000080002120000 0x0000010000424000 0x9da6b90c0733c0e3 0x73b4d72180e6781c

def z1447 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0x77ff3ff1ffc07f05 0xeeffe7fe3ff80fe0

def z1448 : W := mkw 0x0000080002120000 0x0000010000424000 0x9c26b80c073380e3 0x1384d70180e6701c

def z1449 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xffffffffffc07f05 0xfffffffffff80fe0

def z1450 : W := mkw 0x021510959480a6a4 0x0042a212b29014d4 0xc7ff00dd9fc033e1 0xf8ffe01bb3f8067c

def z1451 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xfffffffffffc7fff 0xffffffffffff8fff

def z1452 : W := mkw 0x0000080002120000 0x0000010000424000 0xffe7b90c07f3c0e7 0xfffcf72180fe781c

def z1453 : W := mkw 0x081709b017926a00 0x2102e13602f24d40 0x7a59b9f018f3ff06 0x8f4b373e031e7fe0

def z1454 : W := mkw 0xc808f44f55806a00 0xd9011e89eab00d40 0xfee1fe3fffc07f05 0xffdc3fc7fff80fe0

def z1455 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xffffb9fc1fc07f05 0xfffff73f83f80fe0

def z1456 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xff9fffffe0038087 0x3ff3fffffc007010

def z1457 : W := mkw 0x0000080002120000 0x0000010000424000 0x1da6b80c07338063 0x63b4d70180e6700c

def z1458 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0xfffffff3ffc07f05 0xfffffffe7ff80fe0

def z1459 : W := mkw 0x1a37372595c5cca4 0x6346e6e4b2b8b994 0xa981872d80f04ce6 0x753030e5b01e099c

def z1460 : W := mkw 0x1b021b252357492e 0x23604364a46ae925 0xebe7ff1e67fc43fe 0xfd7cffe3ccff887f

def z1461 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x093ef8001f3f8002 0x4127df0003e7f000

def z1462 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xda19feffe0000000 0x1b433fdffc000000

def z1463 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffe74733e7cfcf9f 0xfffce8e67cf9f9f3

def z1464 : W := mkw 0xac1fc1fa1da87a50 0xb583f83f43b50f4a 0xeee7c03e07fc0fff 0xbddcf807c0ff81ff

def z1465 : W := mkw 0xb508c24aa86d95da 0x96a11849550db2bb 0x77d987fdf8f3ff65 0xeefb30ffbf1e7fec

def z1466 : W := mkw 0x0000080002120000 0x0000010000424000 0xfffeb9cc1f33f0e7 0xffffd73983e67e1c

def z1467 : W := mkw 0x3b3ff725bdedcdae 0xe767fee4b7bdb9b5 0xe259473ff8cc4ffc 0x9c4b28e7ff1989ff

def z1468 : W := mkw 0x303dee001eff0000 0xc607bdc003dfe000 0x7ffffe31ffff8f07 0xefffffc63ffff1e0

def z1469 : W := mkw 0x4a0219b5c312eea4 0x29404336b8625dd4 0xfde6b9fde733ffe7 0x7fbcd73fbce67ffc

def z1470 : W := mkw 0x1015260014c50000 0x4202a4c00298a000 0x1fbf7e001fcf8003 0xe3f7efc003f9f000

def z1471 : W := mkw 0x511737b5e045858a 0x6a22e6f6bc08b0b1 0xeac6780200cf8f9f 0xbd58cf004019f1f3

def z1472 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b90c073380e3 0x77b4d72180e6701c

def z1473 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0xffe7bf3de7f3cfe7 0xfffcf7e7bcfe79fc

def z1474 : W := mkw 0xa408c84a0a3a1050 0x948119094147420a 0xf67e79ce1f0ff0fd 0x9ecfcf39c3e1fe1f

def z1475 : W := mkw 0xbe3ff76f9deddcf4 0xf7c7feedf3bdbb9e 0x425946e398cc3c18 0x884b28dc73198783

def z1476 : W := mkw 0x0000080002120000 0x0000010000424000 0xfde6b9cc0733f0e7 0x7fbcd73980e67e1c

def z1477 : W := mkw 0x6400340548281050 0x4c800680a905020a 0x73d83fc1f83c70fe 0xee7b07f83f078e1f

def z1478 : W := mkw 0xc01ffdff42120000 0xf803ffbfe8424000 0xe23947ffe7338003 0x7c4728fffce67000

def z1479 : W := mkw 0x0000000000000000 0x0000000000000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z1480 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x77ffbffdffc07f05 0xeefff7ffbff80fe0

def z1481 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xffc7ff3fe0cf8f9f 0xbff8ffe7fc19f1f3

def z1482 : W := mkw 0x0000080002120000 0x0000010000424000 0xffe6f90e073fc0ff 0xfffcdf21c0e7f81f

def z1483 : W := mkw 0x8400084a02121050 0x108001094042420a 0x5de6b8c20733b01b 0x6bbcd71840e67603

def z1484 : W := mkw 0xb528ca4aaa7f95da 0x96a51949554ff2bb 0x8800c00e003f80fa 0x11001801c007f01f

def z1485 : W := mkw 0x703dee905eff2200 0xce07bdd20bdfe440 0x5ffffed07fffb303 0xebffffda0ffff660

def z1486 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0x42414633e0cf8f9f 0xa84828c67c19f1f3

def z1487 : W := mkw 0x6c1735b55da87a50 0x6d82e6b6abb50f4a 0x14273e31e7fc0ffb 0x0284e7c63cff81ff

def z1488 : W := mkw 0x00152c0016920000 0x4002a58002d24000 0x1fbfbe001ff38003 0xe3f7f7c003fe7000

def z1489 : W := mkw 0x0000080002120000 0x0000010000424000 0x3da6b90c0733c067 0x67b4d72180e6780c

def z1490 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x157f3ff1ffc07f05 0xe2afe7fe3ff80fe0

def z1491 : W := mkw 0x11000a00a257858a 0x02200140144af0b1 0x0060000007ffcfff 0xe00c000000fff9ff

def z1492 : W := mkw 0xd91ff7fff5c5ef8a 0xfb23fefffeb8bdf1 0x013eb9cc1f0ff09a 0x4027d73983e1fe13

def z1493 : W := mkw 0x0000080002120000 0x0000010000424000 0xa9a6b90c0733c0e7 0x7534d72180e6781c

def z1494 : W := mkw 0x702adbb55eff0000 0xae055b76abdfe000 0x0bb8c031ffff8003 0xe17718063ffff000

def z1495 : W := mkw 0x0000080002120000 0x0000010000424000 0xffe7b93c07f3cfe7 0xfffcf72780fe79fc

def z1496 : W := mkw 0x191703b0b5c5ef8a 0x2322e07616b8bdf1 0xfbfe47c3ff0ff09e 0xff7fc8f87fe1fe13

def z1497 : W := mkw 0xca1de4dac100cca4 0xd943bc9b58201994 0x5f9ffed260004ce4 0x0bf3ffda4c00099c

def z1498 : W := mkw 0x74221bb55eff1050 0x2e844376abdfe20a 0x00600031fffff0ff 0xe00c00063ffffe1f

def z1499 : W := mkw 0xd02adbff56d70000 0xba055b7feadae000 0xebb8c1ffe7c38001 0x1d77183ffcf87000

def z1500 : W := mkw 0xf51ff7ffe86d95da 0xfea3fefffd0db2bb 0x011eb9cc18f3ff61 0x4023d739831e7fec

def z1501 : W := mkw 0xc81ff5ff55806a00 0xf903febfeab00d40 0x9c67fe3fffc07f05 0xf38cffc7fff80fe0

def z1502 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0xffbfffffe7004005 0x7ff7fffffce00800

def z1503 : W := mkw 0x02000800821284a4 0x0040010010425094 0x9da6b80c073380e3 0x73b4d70180e6701c

def z1504 : W := mkw 0xa408c04a08281050 0x948118094105020a 0xffdffffff83c70fe 0xfffbffffff078e1f

def z1505 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xf7ff3ffdffc07f05 0xfeffe7ffbff80fe0

def z1506 : W := mkw 0x0000080002120000 0x0000010000424000 0xffa7ff3fe733c0e7 0x7ff4ffe7fce6781c

def z1507 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xffffbffdffc07f05 0xfffff7ffbff80fe0

def z1508 : W := mkw 0x0000080002120000 0x0000010000424000 0xfde6b90e0733c0ff 0x7fbcd721c0e6781f

def z1509 : W := mkw 0xf02adbff5eff0000 0xbe055b7febdfe000 0xebb8c1ffffff8003 0xfd77183ffffff000

def z1510 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x567f3ef1ffc03f01 0x8acfe7de3ff807e0

def z1511 : W := mkw 0x11000a00a257858a 0x02200140144af0b1 0xe367fe33e7fc0f9c 0xdc6cffc67cff81f3

def z1512 : W := mkw 0xf42adbff5eff1050 0xbe855b7febdfe20a 0xebf8c1fffffff0ff 0xfd7f183ffffffe1f

def z1513 : W := mkw 0xec08f44f5da87a50 0xdd811e89ebb50f4a 0x9820fe0fe7fc0ffb 0x13041fc1fcff81ff

def z1514 : W := mkw 0xd0221bff56d70000 0x3a04437feadae000 0xe02001ffe7c38001 0x1c04003ffcf87000

def z1515 : W := mkw 0xa53dec4abeba95da 0xd4a7bd8957d752bb 0x013eb9fdff307f60 0x4027d73fbfe60fec

def z1516 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b92c0733cce7 0x77b4d72580e6799c

def z1517 : W := mkw 0xd4221bff56d71050 0x3a84437feadae20a 0xe06001ffe7c3f0fd 0x1c0c003ffcf87e1f

def z1518 : W := mkw 0x081725b015806a00 0x6102e4b602b00d40 0x77ff3ff1ffc07f05 0xeeffe7fe3ff80fe0

def z1519 : W := mkw 0x0000080002120000 0x0000010000424000 0x0126b90c0733c0e7 0x6024d72180e6781c

def z1520 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x7fff7ff1ffc07f05 0xefffeffe3ff80fe0

def z1521 : W := mkw 0x0000080002120000 0x0000010000424000 0x9da6b80c0733c0e7 0x73b4d70180e6781c

def z1522 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xffff3ff1ffc07f05 0xffffe7fe3ff80fe0

def z1523 : W := mkw 0x081711b515806a00 0x2102e236a2b00d40 0xffff7ff3ffc07f05 0xffffeffe7ff80fe0

def z1524 : W := mkw 0xf4221bff5eff1050 0x3e84437febdfe20a 0xe06001fffffff0ff 0xfc0c003ffffffe1f

def z1525 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x77ff7ff3ffc07f05 0xeeffeffe7ff80fe0

def z1526 : W := mkw 0x490211b5e100ef8a 0x29204236bc201df1 0xe04001f3e0007f9c 0x1c08003e7c000ff3

def z1527 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b90c0733c063 0x77b4d72180e6780c

def z1528 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x153f3ff1ffc07f01 0x42a7e7fe3ff80fe0

def z1529 : W := mkw 0x0000080002120000 0x0000010000424000 0xffa7ff0e0733c0e7 0x7ff4ffe1c0e6781c

def z1530 : W := mkw 0x0000080002120000 0x0000010000424000 0x1526b90c0733c061 0x42a4d72180e6780c

def z1531 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0x567f3ef1ffc07f05 0xeacfe7de3ff80fe0

def z1532 : W := mkw 0x481735b555806a00 0x6902e6b6aab00d40 0xffffbffdfff07fe7 0xfffff7ffbffe0ffc

def z1533 : W := mkw 0xb708ca4aaa7f95fe 0x96e11949554ff2bf 0x8800c00e003f80fa 0x11001801c007f01f

def z1534 : W := mkw 0xec1ff5ff5da87a50 0xfd83febfebb50f4a 0xffbfffffe7fc0ffb 0x1ff7fffffcff81ff

def z1535 : W := mkw 0x50221bb556d70000 0x2a044376aadae000 0x00200031e7c38001 0x000400063cf87000

def z1536 : W := mkw 0x0000080002120000 0x0000010000424000 0xbda6b80c073380e7 0x77b4d70180e6701c

def z1537 : W := mkw 0x01352c00b692858a 0x4026a58016d250b1 0xeae67833e70c0f9e 0xbd5ccf067ce181f3

def z1538 : W := mkw 0x0000080002120000 0x0000010000424000 0xb9a6b90c0733c0e6 0x7734d72180e6781c

def z1539 : W := mkw 0x4000340540000000 0x48000680a8000000 0x73d83fc1f8007004 0xee7b07f83f000e00

def z1540 : W := mkw 0xd108f64fe045858a 0xda211ec9fc08b0b1 0x66c1b83c00cf8f9f 0xacd837078019f1f3

def z1541 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x427900f01fc07f05 0xe84f201e03f80fe0

def z1542 : W := mkw 0x4a0211b5c100eea4 0x29404236b8201dd4 0xe04001fde0007fe4 0x1c08003fbc000ffc

def z1543 : W := mkw 0xae0ad16f8928dcf4 0xb5c15a2df1251b9e 0x4bd8c0e3983c3c1a 0xe97b181c73078783

def z1544 : W := mkw 0xa408e44a08281050 0xd4811c894105020a 0xfbd8ffcff83c70fe 0xff7b1ff9ff078e1f

def z1545 : W := mkw 0x4800340555806a00 0x49000680aab00d40 0x73f83fc1ffc07f05 0xee7f07f83ff80fe0

def z1546 : W := mkw 0x11000200a045858a 0x022000401408b0b1 0xda414633e0cf8f9a 0x9b4828c67c19f1f3

def z1547 : W := mkw 0x081701b015806a00 0x2102e03602b00d40 0x437f01f01fc07f00 0xc86fe03e03f80fe0

def z1548 : W := mkw 0xf8221bff4b7f6a00 0x3f04437fe96fed40 0xe04001ffe03fff06 0x1c08003ffc07ffe0

def z1549 : W := mkw 0x0a0219258312cca4 0x21404324b0625994 0x8926b90c0733c0e2 0x5124d72180e6781c

def z1550 : W := mkw 0xc01ff5ff40000000 0xf803febfe8000000 0x431fffffe0000000 0x0863fffffc000000

def z1551 : W := mkw 0x641735b548281050 0x6c82e6b6a905020a 0xfec77e33f83c70fe 0xffd8efc67f078e1f

def z1552 : W := mkw 0xbc2aeffa0b7f7a50 0xf7855dff416fef4a 0x9800fe3e003f8ffa 0x13001fc7c007f1ff

def z1553 : W := mkw 0x3a3ff7b59dedeea4 0xe747fef6b3bdbdd4 0xe25947fd98cc7fe4 0x9c4b28ffb3198ffc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z6,z7,z8,z3,z4,z9])],[(0,[z10,z11,z12,z3,z4,z13]),(0,[z14,z15,z2,z3,z4,z13]),(0,[z16,z7,z15,z2,z4,z17])],[(0,[z7,z15,z2,z18,z4,z13]),(0,[z19,z7,z2,z3,z4,z13]),(0,[z7,z15,z20,z2,z4,z13])],[(0,[z15,z2,z3,z21,z4,z22]),(0,[z7,z15,z2,z23,z4,z24]),(0,[z25,z15,z2,z3,z4,z9])],[(0,[z15,z2,z3,z21,z4,z13]),(0,[z7,z15,z2,z26,z4,z13])],[(0,[z7,z15,z27,z2,z28,z4]),(0,[z7,z15,z2,z29,z4,z13]),(0,[z7,z15,z2,z30,z4,z9]),(0,[z31,z15,z2,z3,z32,z4])],[(0,[z10,z15,z12,z3,z4,z33]),(0,[z7,z15,z2,z4,z34,z35]),(0,[z7,z15,z36,z3,z4,z13]),(0,[z37,z15,z2,z3,z4,z38]),(0,[z15,z2,z3,z39,z21,z4])],[(0,[z7,z15,z2,z3,z4,z40]),(0,[z7,z15,z2,z3,z41,z42]),(0,[z43,z7,z15,z2,z4,z13]),(0,[z7,z44,z2,z23,z4,z13])],[(0,[z7,z15,z45,z3,z4,z13]),(0,[z46,z7,z2,z4,z47,z13])],[(0,[z48,z15,z2,z12,z4,z5]),(0,[z49,z15,z2,z3,z50,z35]),(1,[z46,z7,z2,z32,z4]),(0,[z7,z15,z51,z2,z4,z13])],[(0,[z7,z48,z15,z2,z4,z52]),(0,[z53,z54,z7,z2,z4,z13]),(0,[z7,z48,z15,z2,z4,z55])],[(0,[z7,z15,z2,z3,z4,z56]),(0,[z7,z15,z57,z58,z4,z13]),(0,[z59,z15,z2,z3,z4,z60]),(0,[z46,z7,z2,z4,z61,z13])],[(0,[z7,z62,z63,z2,z4,z13]),(0,[z7,z15,z2,z3,z64,z4])],[(0,[z7,z15,z2,z65,z3,z4])],[(0,[z7,z15,z2,z66,z32,z4]),(0,[z16,z67,z15,z2,z4,z5]),(0,[z68,z15,z2,z3,z4,z5]),(0,[z16,z7,z2,z69,z4,z13])],[(0,[z70,z7,z15,z27,z4,z71])],[(0,[z7,z15,z2,z3,z4,z72]),(0,[z16,z7,z73,z2,z4,z13]),(0,[z49,z15,z2,z3,z74,z13]),(0,[z75,z15,z2,z3,z4,z13]),(0,[z76,z7,z2,z4,z77,z78]),(0,[z46,z7,z2,z4,z13,z79])],[(0,[z7,z15,z2,z3,z80,z13])],[(0,[z7,z15,z81,z2,z4,z13]),(0,[z16,z7,z2,z82,z4,z13]),(0,[z83,z7,z2,z3,z84,z13])],[(0,[z85,z15,z12,z3,z4,z13]),(0,[z15,z2,z3,z21,z4,z5]),(0,[z16,z7,z86,z87,z4,z13]),(0,[z7,z15,z2,z4,z88,z9])],[(0,[z7,z89,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z4,z52]),(0,[z16,z90,z15,z2,z4,z5]),(0,[z16,z59,z2,z3,z4,z13])],[(0,[z91,z15,z2,z3,z92,z13]),(0,[z93,z15,z2,z3,z4,z5]),(0,[z7,z94,z2,z3,z95,z35]),(0,[z7,z15,z2,z96,z34,z13])],[(0,[z91,z15,z97,z3,z4,z5]),(0,[z98,z15,z2,z3,z4,z13])],[(0,[z7,z15,z99,z3,z4,z13])],[],[(0,[z7,z48,z15,z2,z4,z42]),(0,[z7,z15,z2,z100,z4,z101]),(0,[z7,z15,z102,z2,z4,z13])],[(0,[z7,z15,z97,z3,z4,z103])],[(0,[z7,z15,z2,z3,z4,z104]),(0,[z7,z15,z2,z3,z4,z105]),(0,[z7,z15,z2,z106,z77,z13]),(0,[z7,z15,z2,z3,z4,z107])],[(0,[z7,z108,z15,z2,z4,z13]),(0,[z7,z109,z110,z2,z4,z13]),(0,[z16,z7,z15,z2,z111,z13]),(0,[z7,z94,z2,z3,z32,z95])],[(0,[z7,z15,z2,z112,z4,z13]),(0,[z113,z15,z2,z3,z32,z4]),(0,[z7,z2,z4,z114,z77,z13])],[(0,[z7,z15,z2,z3,z4,z115]),(0,[z7,z15,z2,z3,z4,z116]),(0,[z7,z15,z2,z3,z4,z117]),(0,[z46,z7,z2,z118,z4,z13])]],
   [[(0,[z16,z7,z15,z2,z4,z103]),(0,[z16,z7,z15,z2,z4,z119]),(0,[z7,z15,z2,z3,z120,z121])],[(0,[z7,z15,z122,z2,z4,z35]),(0,[z7,z15,z2,z123,z4,z9])],[(0,[z7,z15,z81,z2,z4,z5]),(0,[z124,z15,z2,z3,z4,z5]),(0,[z125,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z126,z4,z13]),(0,[z7,z2,z3,z95,z127,z13]),(0,[z7,z15,z2,z4,z128,z13]),(0,[z37,z15,z2,z23,z4,z13])],[(0,[z129,z15,z2,z130,z4,z13])],[(0,[z7,z15,z2,z3,z4,z42]),(0,[z7,z15,z2,z131,z4,z35]),(0,[z54,z7,z15,z2,z132,z13]),(0,[z133,z15,z2,z3,z28,z4])],[(0,[z7,z15,z2,z4,z77,z13]),(0,[z134,z7,z15,z2,z4,z13]),(0,[z7,z135,z27,z2,z4,z13]),(0,[z7,z15,z2,z136,z4,z9])],[(0,[z137,z15,z138,z3,z4,z40]),(0,[z139,z7,z2,z3,z4,z35]),(0,[z140,z15,z2,z141,z4,z13]),(0,[z70,z16,z7,z15,z4,z71])],[(0,[z7,z15,z2,z142,z4,z13]),(0,[z7,z15,z2,z3,z143,z13]),(0,[z7,z144,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z145,z13])],[(0,[z7,z146,z2,z3,z4,z13]),(0,[z147,z15,z2,z141,z4,z13]),(0,[z46,z7,z2,z141,z4,z13]),(0,[z7,z15,z2,z3,z121,z13]),(0,[z7,z148,z2,z4,z114,z13])],[(0,[z16,z7,z15,z149,z4,z13])],[(0,[z7,z11,z2,z3,z4,z9]),(0,[z7,z150,z2,z3,z4,z151]),(0,[z7,z15,z2,z3,z4,z152]),(0,[z7,z15,z2,z3,z153,z35]),(0,[z7,z15,z2,z154,z4,z13])],[(0,[z129,z15,z2,z155,z4,z13]),(0,[z7,z15,z2,z3,z156,z9]),(0,[z53,z7,z2,z3,z84,z35]),(0,[z7,z15,z2,z3,z4,z157])],[(0,[z7,z158,z15,z2,z4,z13]),(0,[z76,z7,z2,z3,z4,z78])],[(0,[z7,z2,z4,z114,z77,z5]),(0,[z7,z159,z27,z2,z4,z13]),(0,[z46,z7,z2,z4,z160,z13])],[(0,[z0,z161,z2,z3,z4,z5]),(0,[z46,z162,z7,z2,z4,z13])],[(0,[z7,z15,z2,z3,z163,z4]),(0,[z164,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z4,z13,z165]),(0,[z7,z15,z2,z4,z166,z9])],[(0,[z7,z15,z2,z167,z4,z13])],[(0,[z16,z7,z15,z2,z168,z9]),(0,[z140,z15,z169,z2,z4,z13])],[(0,[z7,z15,z2,z3,z170,z4]),(0,[z91,z15,z2,z3,z21,z4]),(0,[z7,z15,z171,z3,z168,z13])],[(0,[z16,z7,z2,z172,z4,z13]),(0,[z7,z15,z2,z4,z173,z13]),(0,[z59,z15,z2,z3,z4,z9]),(0,[z7,z174,z2,z3,z4,z13]),(0,[z175,z7,z15,z3,z41,z13]),(0,[z7,z15,z2,z176,z4,z13])],[(0,[z7,z15,z2,z4,z77,z5]),(0,[z16,z7,z2,z32,z177,z4]),(0,[z7,z15,z178,z4,z61,z13])],[(0,[z7,z179,z2,z3,z4,z13]),(0,[z46,z7,z2,z180,z4,z13]),(0,[z46,z7,z2,z181,z4,z13])],[(0,[z182,z15,z2,z3,z92,z13])],[(0,[z49,z15,z2,z3,z50,z183]),(0,[z7,z15,z2,z184,z4,z35]),(0,[z134,z7,z185,z2,z4,z13])],[(0,[z91,z15,z2,z3,z74,z13]),(0,[z16,z186,z15,z2,z4,z13]),(0,[z7,z48,z15,z2,z4,z24]),(0,[z46,z7,z2,z4,z187,z13])],[(0,[z7,z15,z188,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z189]),(0,[z190,z7,z2,z3,z4,z191]),(0,[z7,z15,z192,z193,z4,z35]),(0,[z15,z2,z58,z3,z21,z4]),(0,[z7,z185,z27,z2,z4,z13]),(0,[z7,z15,z2,z194,z77,z13])],[(0,[z129,z15,z2,z155,z4,z5]),(0,[z7,z15,z2,z4,z35,z195]),(0,[z7,z48,z15,z2,z196,z4]),(0,[z7,z15,z2,z3,z4,z197]),(0,[z7,z15,z2,z4,z77,z198]),(0,[z199,z46,z7,z2,z4,z13]),(0,[z200,z7,z15,z2,z3,z4])],[(0,[z7,z15,z2,z3,z4,z201])],[(0,[z7,z15,z2,z3,z202,z13]),(0,[z91,z15,z2,z3,z4,z183]),(0,[z203,z15,z2,z3,z4,z9]),(0,[z15,z2,z32,z21,z4,z77])],[(0,[z7,z15,z2,z143,z77,z13]),(0,[z204,z7,z15,z2,z3,z4]),(0,[z140,z15,z2,z3,z4,z5])],[(0,[z7,z15,z2,z66,z4,z205]),(0,[z7,z15,z2,z206,z4,z13]),(0,[z7,z158,z185,z2,z4,z13])],[(0,[z15,z2,z3,z207,z4,z5]),(0,[z147,z15,z2,z3,z4,z5]),(0,[z46,z7,z2,z3,z4,z5]),(0,[z7,z44,z3,z4,z41,z13]),(0,[z7,z15,z27,z2,z32,z77])]],
   [[(0,[z7,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z208,z4,z35]),(0,[z16,z7,z48,z2,z4,z9])],[(0,[z7,z209,z8,z3,z4,z13]),(0,[z53,z16,z7,z2,z132,z13]),(0,[z16,z7,z2,z4,z114,z13]),(0,[z15,z210,z2,z3,z21,z4]),(0,[z15,z2,z3,z32,z211,z4])],[(0,[z175,z7,z15,z3,z41,z5]),(0,[z7,z48,z15,z2,z4,z212]),(0,[z7,z15,z2,z3,z4,z24])],[(0,[z213,z7,z15,z2,z3,z4]),(0,[z137,z15,z138,z4,z77,z13]),(1,[z7,z15,z3,z214,z13]),(0,[z7,z185,z2,z3,z215,z13])],[(0,[z216,z7,z15,z2,z4,z35]),(0,[z7,z15,z2,z217,z3,z4]),(0,[z37,z15,z2,z3,z41,z13]),(0,[z7,z15,z2,z3,z196,z4]),(0,[z7,z15,z27,z2,z4,z218])],[(0,[z219,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z4,z220,z13]),(0,[z7,z15,z2,z221,z3,z32])],[(0,[z137,z15,z2,z3,z222,z13]),(0,[z15,z223,z2,z50,z4,z5]),(0,[z7,z44,z2,z3,z4,z13]),(0,[z48,z15,z224,z2,z4,z13])],[(0,[z225,z7,z226,z2,z3,z4])],[(0,[z7,z15,z2,z3,z4,z227]),(0,[z7,z15,z2,z3,z132,z9]),(0,[z7,z48,z185,z2,z4,z13]),(0,[z7,z228,z2,z3,z4,z13])],[(0,[z7,z15,z2,z229,z3,z13])],[(0,[z7,z15,z2,z3,z4,z230]),(0,[z7,z15,z3,z168,z41,z9])],[(0,[z16,z7,z1,z2,z4,z9]),(0,[z7,z110,z2,z3,z4,z9]),(0,[z7,z15,z2,z3,z4,z231])],[(0,[z90,z15,z2,z3,z21,z4]),(0,[z7,z226,z15,z2,z3,z215]),(0,[z232,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z212]),(0,[z46,z7,z2,z180,z77,z13]),(0,[z233,z15,z2,z3,z4,z13])],[(0,[z113,z15,z2,z3,z4,z205]),(0,[z7,z15,z2,z234,z208,z32])],[(0,[z113,z48,z15,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z235])],[(0,[z7,z15,z2,z3,z4,z5]),(0,[z236,z1,z2,z3,z4,z13]),(0,[z16,z15,z2,z32,z21,z4])],[(0,[z237,z1,z2,z3,z4,z13]),(0,[z7,z15,z2,z32,z4,z238]),(0,[z7,z15,z239,z2,z4,z13]),(0,[z7,z27,z2,z4,z114,z13])],[(0,[z7,z15,z2,z3,z240,z13]),(0,[z7,z15,z2,z3,z168,z52]),(0,[z7,z241,z2,z3,z4,z35]),(0,[z15,z224,z2,z3,z4,z13]),(0,[z7,z15,z2,z123,z32,z4]),(0,[z7,z15,z2,z3,z4,z242]),(0,[z243,z15,z2,z3,z4,z13]),(0,[z70,z46,z7,z2,z4,z13])],[(0,[z49,z15,z149,z3,z4,z13]),(0,[z15,z2,z3,z244,z21,z4]),(0,[z7,z15,z2,z3,z4,z245]),(0,[z7,z15,z210,z3,z168,z246]),(0,[z7,z15,z2,z3,z4,z247])],[(0,[z137,z48,z15,z2,z4,z5]),(0,[z7,z15,z2,z248,z4,z13]),(0,[z249,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z250,z4,z13]),(0,[z46,z7,z2,z100,z4,z13]),(0,[z251,z15,z2,z3,z21,z4])],[(0,[z252,z15,z2,z3,z21,z4]),(0,[z91,z15,z2,z3,z156,z4]),(0,[z7,z15,z2,z3,z253,z9])],[(0,[z7,z44,z2,z3,z4,z5]),(0,[z7,z15,z2,z254,z77,z13]),(0,[z7,z15,z2,z3,z4,z198])],[(0,[z7,z15,z2,z234,z3,z156]),(0,[z7,z15,z2,z255,z4,z35]),(0,[z37,z48,z15,z2,z4,z13])],[(0,[z139,z256,z2,z141,z4,z13]),(0,[z7,z15,z2,z4,z13,z257])],[(0,[z15,z1,z2,z3,z4,z183]),(0,[z7,z15,z2,z66,z4,z5]),(0,[z7,z15,z2,z3,z4,z258]),(0,[z259,z7,z8,z3,z4,z13]),(0,[z7,z15,z2,z4,z260,z13]),(0,[z16,z7,z2,z32,z95,z4]),(0,[z261,z15,z2,z3,z21,z4])],[],[],[(0,[z7,z15,z2,z4,z77,z262])],[(0,[z7,z15,z263,z2,z4,z9]),(0,[z225,z264,z15,z2,z3,z4]),(0,[z249,z15,z2,z3,z4,z265])],[(0,[z7,z15,z2,z4,z77,z266]),(0,[z7,z2,z267,z268,z4,z13]),(0,[z7,z15,z269,z2,z4,z187])],[(0,[z137,z15,z138,z3,z4,z13]),(0,[z7,z270,z2,z3,z4,z13]),(0,[z49,z63,z2,z3,z4,z13]),(0,[z16,z7,z2,z95,z4,z35]),(0,[z7,z271,z15,z2,z4,z13])],[(0,[z7,z15,z2,z272,z4,z13]),(0,[z16,z7,z15,z2,z4,z273]),(0,[z7,z135,z2,z23,z4,z13]),(0,[z7,z15,z27,z2,z234,z32]),(0,[z274,z7,z15,z2,z275,z4])]],
   [[(0,[z37,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z168,z42]),(0,[z16,z133,z15,z2,z32,z4]),(0,[z7,z2,z3,z267,z4,z13]),(0,[z7,z15,z2,z215,z77,z13]),(0,[z7,z15,z2,z96,z276,z13])],[(0,[z7,z15,z2,z3,z277,z13]),(0,[z7,z15,z2,z4,z278,z13]),(0,[z279,z46,z7,z2,z4,z13])],[(0,[z7,z1,z263,z2,z4,z13]),(0,[z16,z7,z15,z2,z280,z13]),(0,[z281,z15,z2,z3,z4,z13])],[(0,[z282,z15,z2,z3,z4,z5]),(0,[z129,z15,z2,z155,z4,z266]),(0,[z59,z15,z2,z3,z32,z4]),(0,[z7,z15,z2,z283,z4,z13]),(0,[z7,z15,z2,z4,z284,z13]),(0,[z274,z7,z15,z2,z4,z285]),(0,[z286,z15,z27,z2,z4,z13])],[(0,[z46,z7,z2,z4,z287,z13])],[(0,[z7,z15,z2,z3,z288,z4]),(0,[z289,z15,z2,z3,z4,z5]),(0,[z16,z7,z15,z2,z4,z246])],[(0,[z7,z15,z2,z290,z4,z13]),(0,[z7,z15,z2,z3,z4,z291])],[(0,[z7,z292,z293,z2,z4,z13]),(0,[z16,z7,z2,z294,z4,z13]),(0,[z59,z2,z295,z3,z4,z13]),(0,[z186,z15,z27,z2,z4,z13]),(0,[z296,z46,z7,z2,z4,z13])],[(0,[z46,z49,z7,z2,z4,z13]),(0,[z7,z15,z2,z297,z4,z5]),(0,[z7,z15,z298,z2,z4,z13])],[(0,[z216,z7,z86,z2,z4,z13]),(0,[z7,z299,z2,z3,z4,z13]),(0,[z7,z48,z110,z2,z4,z13]),(0,[z7,z15,z97,z300,z4,z13]),(0,[z7,z15,z2,z3,z4,z301]),(0,[z302,z7,z15,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z303]),(0,[z16,z304,z15,z2,z4,z13]),(0,[z7,z15,z192,z305,z193,z4]),(0,[z70,z186,z15,z3,z4,z71])],[(0,[z252,z1,z27,z2,z4,z13]),(0,[z15,z2,z12,z3,z222,z13]),(0,[z7,z306,z2,z3,z4,z13]),(0,[z7,z15,z2,z307,z4,z13]),(0,[z7,z308,z27,z2,z4,z13]),(0,[z274,z7,z15,z2,z4,z309])],[(0,[z16,z137,z15,z2,z4,z5])],[(0,[z7,z310,z2,z3,z4,z13]),(0,[z7,z63,z2,z3,z4,z9]),(0,[z311,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z312,z4,z13])],[(0,[z313,z15,z2,z3,z92,z13]),(0,[z7,z94,z2,z95,z77,z13])],[(0,[z7,z15,z2,z3,z92,z314]),(0,[z37,z15,z2,z3,z4,z5]),(0,[z315,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z4,z316]),(0,[z175,z7,z15,z3,z214,z13])],[(0,[z7,z15,z2,z300,z4,z35]),(0,[z7,z15,z2,z317,z4,z13]),(0,[z7,z15,z2,z318,z4,z13]),(0,[z319,z7,z15,z2,z4,z13])],[(0,[z16,z7,z320,z2,z4,z13]),(0,[z7,z15,z2,z4,z321,z13]),(0,[z16,z7,z15,z2,z4,z322]),(0,[z186,z15,z2,z3,z215,z13]),(0,[z7,z15,z2,z3,z323,z4])],[(0,[z91,z15,z2,z3,z4,z324]),(0,[z7,z15,z2,z4,z284,z5]),(0,[z16,z7,z15,z2,z325,z4])],[(0,[z7,z15,z2,z3,z4,z326]),(0,[z7,z327,z2,z3,z32,z4])],[(0,[z15,z328,z2,z3,z4,z5]),(0,[z7,z329,z2,z3,z4,z13]),(0,[z7,z48,z15,z2,z28,z4]),(0,[z7,z15,z2,z330,z4,z9])],[(0,[z7,z15,z2,z180,z331,z13]),(0,[z7,z15,z3,z4,z214,z13]),(0,[z7,z308,z2,z3,z215,z13])],[(0,[z15,z332,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z4,z262]),(0,[z7,z27,z2,z114,z77,z13])],[(0,[z7,z150,z2,z4,z77,z13]),(0,[z7,z15,z2,z3,z333,z13]),(0,[z7,z15,z2,z334,z4,z13]),(0,[z16,z7,z15,z2,z215,z13]),(0,[z274,z7,z15,z2,z4,z335]),(0,[z7,z48,z159,z2,z4,z13]),(0,[z7,z185,z2,z3,z32,z4]),(0,[z7,z15,z2,z3,z336,z13])],[(0,[z7,z15,z2,z3,z4,z266])],[(0,[z337,z1,z2,z3,z4,z13]),(0,[z7,z15,z338,z2,z4,z13]),(0,[z7,z150,z2,z3,z143,z13]),(1,[z15,z12,z3,z222,z13]),(0,[z7,z15,z2,z339,z4,z13]),(0,[z7,z15,z27,z2,z41,z9])],[(0,[z7,z15,z27,z2,z4,z340]),(0,[z7,z1,z2,z330,z4,z13]),(0,[z7,z15,z2,z4,z77,z341]),(0,[z7,z342,z2,z3,z4,z13]),(0,[z304,z15,z2,z343,z4,z13])],[(0,[z16,z7,z1,z2,z32,z4]),(0,[z161,z7,z263,z2,z4,z13]),(0,[z7,z110,z2,z3,z32,z4]),(0,[z7,z15,z2,z3,z4,z344])],[(0,[z16,z7,z2,z8,z4,z9]),(0,[z15,z2,z295,z3,z21,z4]),(0,[z7,z15,z345,z3,z32,z4]),(0,[z53,z7,z2,z3,z84,z119])],[(0,[z15,z12,z3,z92,z41,z13]),(0,[z7,z15,z2,z346,z4,z13]),(0,[z347,z7,z15,z2,z4,z13]),(0,[z249,z15,z2,z123,z4,z13])],[(0,[z7,z15,z2,z348,z77,z13]),(0,[z91,z46,z7,z2,z4,z13]),(0,[z7,z15,z2,z3,z28,z4]),(0,[z7,z15,z27,z2,z349,z13])],[(0,[z7,z15,z2,z350,z4,z13]),(0,[z7,z15,z2,z4,z351,z9]),(0,[z7,z15,z2,z181,z4,z79]),(0,[z352,z15,z27,z2,z4,z13])]],
   [[(0,[z353,z1,z2,z3,z4,z13]),(0,[z16,z7,z241,z2,z4,z13])],[(0,[z225,z7,z308,z2,z3,z4]),(0,[z7,z15,z2,z4,z13,z354])],[(0,[z15,z2,z12,z3,z4,z5]),(0,[z7,z15,z355,z3,z4,z9]),(0,[z175,z7,z15,z77,z41,z13])],[(0,[z7,z15,z2,z3,z4,z356])],[(0,[z7,z15,z2,z3,z4,z357]),(0,[z16,z7,z2,z4,z358,z13]),(0,[z7,z48,z359,z2,z4,z13]),(0,[z7,z15,z2,z3,z32,z360]),(0,[z46,z7,z2,z4,z4,z13])],[],[(0,[z16,z7,z332,z2,z4,z13]),(0,[z15,z2,z3,z361,z4,z5]),(0,[z7,z15,z2,z3,z362,z9]),(0,[z7,z15,z363,z2,z4,z13]),(0,[z46,z7,z2,z364,z4,z13])],[(0,[z7,z15,z365,z2,z4,z13]),(0,[z15,z2,z366,z4,z77,z13])],[(0,[z7,z15,z2,z3,z4,z367]),(0,[z91,z15,z149,z3,z4,z5]),(0,[z53,z16,z7,z2,z84,z13]),(0,[z368,z48,z15,z2,z4,z13]),(0,[z7,z15,z2,z4,z369,z13]),(0,[z7,z15,z2,z4,z370,z13])],[(0,[z7,z15,z2,z3,z32,z371])],[],[(0,[z15,z2,z3,z4,z74,z13])],[(0,[z10,z15,z12,z372,z4,z13]),(0,[z7,z15,z149,z3,z4,z103]),(0,[z7,z15,z2,z346,z4,z5]),(0,[z7,z15,z263,z2,z32,z4]),(0,[z7,z15,z27,z2,z4,z373])],[(0,[z15,z2,z3,z74,z92,z13]),(0,[z133,z15,z2,z3,z4,z35]),(0,[z16,z374,z7,z2,z4,z13]),(0,[z7,z375,z2,z4,z77,z13])],[(0,[z7,z15,z376,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z377]),(0,[z7,z15,z2,z3,z4,z378])],[(0,[z7,z15,z2,z379,z4,z35]),(0,[z16,z7,z8,z4,z41,z13]),(0,[z16,z7,z2,z345,z4,z13]),(0,[z7,z15,z2,z380,z4,z13])],[],[],[(0,[z7,z150,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z381,z35])],[(0,[z1,z2,z3,z4,z382,z5]),(0,[z161,z7,z2,z330,z4,z13]),(0,[z7,z15,z27,z2,z96,z5])],[(0,[z16,z161,z7,z2,z4,z35]),(0,[z7,z15,z2,z4,z77,z383]),(0,[z91,z63,z2,z3,z4,z5]),(0,[z7,z94,z2,z3,z384,z95]),(0,[z7,z15,z2,z118,z385,z4])],[(0,[z7,z15,z2,z386,z4,z13]),(0,[z7,z15,z387,z2,z4,z13]),(0,[z388,z7,z2,z4,z77,z13])],[(0,[z0,z15,z2,z3,z4,z389]),(0,[z390,z7,z15,z2,z32,z4])],[(0,[z15,z27,z2,z391,z4,z5]),(0,[z16,z392,z15,z2,z4,z13]),(0,[z304,z308,z2,z3,z4,z13])],[(0,[z7,z63,z2,z3,z4,z103]),(0,[z7,z15,z2,z4,z393,z13])],[(0,[z7,z15,z2,z384,z4,z88])],[(0,[z7,z15,z2,z4,z394,z13]),(0,[z16,z7,z2,z395,z4,z13])],[(0,[z7,z15,z2,z3,z4,z396]),(0,[z304,z15,z2,z3,z4,z35]),(0,[z397,z15,z2,z3,z4,z35]),(0,[z249,z15,z2,z3,z4,z398]),(0,[z53,z7,z2,z84,z77,z13]),(0,[z7,z15,z2,z3,z4,z399]),(0,[z7,z15,z27,z2,z276,z13])],[(0,[z49,z15,z2,z3,z400,z13]),(0,[z7,z15,z2,z4,z77,z401]),(0,[z15,z2,z3,z130,z4,z13]),(0,[z7,z15,z2,z402,z77,z13]),(0,[z37,z15,z2,z3,z168,z13]),(0,[z70,z304,z15,z3,z4,z71]),(0,[z15,z2,z3,z366,z4,z13])],[(0,[z252,z1,z2,z3,z4,z389]),(0,[z7,z15,z2,z403,z4,z13]),(0,[z7,z135,z2,z3,z4,z13])],[(0,[z404,z1,z2,z3,z4,z13]),(0,[z7,z15,z2,z66,z4,z341]),(0,[z405,z15,z2,z3,z21,z4]),(0,[z46,z46,z7,z2,z4,z13])],[(0,[z16,z7,z15,z2,z4,z389])]],
   [[(0,[z7,z15,z2,z3,z41,z218])],[(0,[z7,z150,z2,z3,z4,z5]),(0,[z6,z16,z7,z8,z4,z13])],[(0,[z7,z15,z2,z3,z4,z406])],[],[(0,[z407,z16,z7,z2,z4,z13]),(0,[z7,z15,z2,z408,z4,z13]),(0,[z7,z15,z2,z330,z32,z4])],[(0,[z19,z7,z2,z50,z4,z13]),(0,[z7,z159,z2,z3,z4,z13]),(0,[z53,z7,z15,z2,z331,z13])],[],[(0,[z186,z15,z2,z3,z4,z40]),(0,[z7,z48,z15,z2,z4,z189]),(0,[z7,z15,z2,z3,z4,z409]),(0,[z70,z7,z15,z410,z3,z4])],[(0,[z7,z94,z2,z3,z411,z13]),(0,[z7,z293,z2,z3,z4,z9]),(0,[z15,z2,z3,z32,z21,z9])],[(0,[z7,z412,z413,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z414])],[(0,[z10,z15,z12,z3,z32,z4]),(0,[z7,z15,z2,z415,z4,z13])],[(0,[z416,z15,z2,z3,z4,z40]),(0,[z7,z417,z15,z2,z4,z13]),(0,[z7,z135,z2,z3,z4,z5]),(0,[z15,z2,z3,z21,z4,z35]),(0,[z16,z7,z2,z8,z32,z4]),(0,[z7,z15,z27,z2,z77,z9])],[(0,[z16,z7,z15,z2,z4,z40]),(0,[z7,z15,z355,z3,z4,z119]),(0,[z7,z15,z418,z2,z4,z9]),(0,[z7,z15,z2,z4,z419,z9]),(0,[z7,z15,z420,z2,z234,z32])],[(0,[z421,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z343,z121,z13])],[(0,[z7,z15,z2,z3,z4,z383]),(0,[z422,z7,z8,z3,z4,z13]),(0,[z54,z7,z15,z2,z32,z4])],[(0,[z7,z423,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z4,z189]),(0,[z7,z15,z2,z424,z4,z13])],[(0,[z7,z11,z2,z3,z4,z151]),(0,[z7,z15,z2,z3,z4,z425]),(0,[z426,z15,z2,z3,z4,z5]),(0,[z7,z48,z15,z2,z4,z218])],[(0,[z7,z15,z2,z4,z427,z13])],[(0,[z7,z15,z2,z372,z4,z9]),(0,[z7,z15,z2,z3,z428,z222]),(0,[z7,z159,z2,z3,z4,z5]),(0,[z46,z7,z2,z4,z331,z13])],[(0,[z15,z2,z4,z47,z77,z5]),(0,[z429,z7,z48,z2,z4,z13]),(0,[z7,z48,z2,z4,z13,z430])],[(0,[z15,z12,z3,z4,z41,z5]),(0,[z49,z15,z2,z3,z50,z9]),(0,[z7,z48,z15,z2,z4,z431]),(0,[z53,z7,z355,z3,z84,z13]),(0,[z7,z15,z2,z3,z432,z4]),(0,[z7,z15,z210,z3,z214,z13])],[(0,[z7,z15,z2,z433,z4,z13]),(0,[z7,z15,z2,z434,z4,z13]),(0,[z7,z15,z2,z156,z4,z77]),(0,[z7,z15,z122,z210,z168,z13])],[(0,[z7,z15,z2,z4,z435,z13]),(0,[z76,z390,z7,z2,z4,z78]),(0,[z7,z15,z2,z3,z436,z4])],[(0,[z7,z15,z2,z4,z13,z437]),(0,[z49,z15,z223,z2,z50,z13]),(0,[z7,z15,z2,z3,z4,z438]),(0,[z175,z7,z48,z15,z41,z13]),(0,[z7,z15,z2,z3,z215,z71])],[(0,[z7,z15,z2,z4,z77,z439]),(0,[z7,z15,z81,z2,z4,z35]),(0,[z16,z98,z15,z2,z4,z13]),(0,[z7,z15,z2,z440,z4,z13])],[(0,[z15,z12,z3,z4,z222,z13]),(0,[z7,z441,z2,z3,z4,z13]),(0,[z7,z442,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z443,z215]),(0,[z15,z2,z3,z21,z444,z4])],[(0,[z445,z7,z15,z2,z4,z13]),(0,[z91,z15,z27,z2,z4,z5]),(0,[z7,z15,z2,z3,z4,z218]),(0,[z203,z15,z2,z3,z4,z446]),(0,[z7,z447,z2,z3,z4,z13]),(0,[z7,z15,z2,z180,z32,z77])],[(0,[z7,z448,z2,z3,z4,z13]),(0,[z7,z15,z2,z449,z4,z13]),(0,[z7,z15,z2,z3,z450,z9])],[(0,[z7,z15,z2,z3,z4,z451]),(0,[z7,z15,z2,z452,z4,z13]),(0,[z7,z15,z2,z453,z4,z13]),(0,[z46,z7,z2,z4,z13,z71])],[(0,[z7,z15,z2,z454,z4,z13]),(0,[z7,z423,z2,z3,z4,z5]),(0,[z7,z15,z58,z317,z4,z13])]],
   [[(0,[z0,z15,z2,z3,z4,z42]),(0,[z7,z15,z27,z2,z4,z103]),(0,[z7,z15,z2,z3,z4,z431]),(0,[z7,z15,z27,z2,z4,z119])],[(0,[z16,z7,z86,z2,z4,z9]),(0,[z7,z15,z2,z455,z4,z13])],[(0,[z7,z15,z2,z3,z4,z456]),(0,[z457,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z32,z9])],[(0,[z7,z15,z2,z3,z4,z458]),(0,[z7,z15,z2,z459,z4,z13])],[(0,[z139,z7,z27,z2,z4,z13])],[(0,[z7,z15,z97,z4,z77,z13]),(0,[z7,z15,z2,z4,z460,z13]),(0,[z7,z2,z4,z114,z77,z35]),(0,[z461,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z343,z4,z13])],[(0,[z46,z7,z226,z2,z4,z13]),(0,[z7,z15,z2,z4,z462,z13]),(0,[z186,z15,z2,z3,z121,z13])],[(0,[z16,z7,z2,z463,z4,z13]),(0,[z7,z15,z2,z4,z464,z79]),(0,[z7,z48,z2,z295,z4,z9]),(0,[z7,z15,z2,z3,z465,z9])],[(0,[z16,z7,z15,z2,z4,z42]),(0,[z48,z15,z2,z32,z21,z4]),(0,[z53,z7,z27,z2,z84,z13])],[(0,[z7,z15,z2,z466,z77,z13]),(0,[z7,z15,z2,z3,z4,z467]),(0,[z7,z15,z2,z468,z4,z13])],[(0,[z7,z15,z2,z3,z244,z4]),(0,[z7,z15,z2,z469,z4,z13]),(0,[z16,z7,z81,z2,z4,z13]),(0,[z225,z470,z15,z2,z3,z4]),(0,[z7,z308,z2,z3,z121,z13])],[(0,[z16,z7,z15,z2,z143,z13]),(0,[z7,z15,z2,z4,z77,z35]),(0,[z7,z148,z15,z2,z4,z13]),(0,[z53,z16,z7,z2,z32,z4]),(0,[z7,z345,z295,z3,z4,z13]),(0,[z7,z94,z418,z2,z95,z13]),(0,[z7,z15,z2,z465,z77,z13])],[(0,[z7,z292,z2,z295,z4,z13]),(0,[z7,z15,z2,z453,z4,z5]),(0,[z16,z7,z15,z2,z121,z13]),(0,[z7,z48,z15,z2,z234,z32])],[(0,[z7,z15,z471,z2,z4,z13]),(0,[z7,z292,z15,z2,z32,z4]),(0,[z7,z15,z2,z3,z143,z35])],[(0,[z7,z15,z2,z3,z121,z35]),(0,[z15,z2,z3,z21,z21,z4])],[(0,[z7,z15,z2,z3,z4,z472]),(0,[z0,z15,z2,z4,z77,z5]),(0,[z7,z473,z2,z3,z4,z13]),(0,[z7,z15,z27,z2,z4,z474])],[(0,[z7,z15,z2,z475,z4,z13]),(0,[z15,z2,z3,z476,z21,z4])],[(0,[z16,z477,z7,z2,z4,z13]),(0,[z129,z15,z2,z155,z4,z35]),(0,[z478,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z479]),(0,[z7,z15,z210,z3,z168,z13]),(0,[z70,z7,z15,z3,z4,z480])],[],[(0,[z63,z2,z3,z4,z92,z13]),(1,[z15,z149,z3,z4,z5])],[(0,[z7,z15,z2,z481,z77,z13]),(0,[z15,z2,z391,z3,z4,z5]),(0,[z7,z15,z2,z343,z4,z5]),(0,[z7,z15,z2,z3,z482,z4]),(0,[z186,z48,z15,z2,z4,z13]),(0,[z7,z15,z2,z4,z483,z13])],[(0,[z7,z15,z223,z2,z32,z4]),(0,[z6,z7,z8,z4,z77,z13]),(0,[z7,z15,z8,z3,z41,z9]),(0,[z7,z15,z3,z41,z484,z9]),(0,[z7,z485,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z4,z486]),(0,[z7,z15,z2,z3,z4,z487])],[(0,[z15,z1,z27,z2,z4,z5]),(0,[z7,z293,z2,z3,z32,z4]),(0,[z7,z15,z2,z488,z3,z4]),(0,[z7,z15,z2,z3,z489,z9])],[(0,[z15,z210,z12,z3,z4,z5]),(0,[z7,z15,z2,z3,z490,z13]),(0,[z7,z15,z345,z100,z4,z13]),(0,[z46,z7,z94,z2,z4,z13]),(0,[z37,z15,z2,z3,z4,z438])],[(0,[z7,z15,z491,z2,z4,z13]),(0,[z175,z7,z15,z3,z41,z35]),(0,[z59,z15,z2,z3,z4,z101]),(0,[z7,z15,z2,z492,z77,z13]),(0,[z7,z15,z2,z3,z120,z9])],[(0,[z7,z148,z15,z2,z4,z5]),(0,[z16,z416,z15,z2,z4,z35]),(0,[z7,z15,z493,z2,z4,z13]),(0,[z304,z15,z2,z3,z4,z71])],[(0,[z7,z15,z2,z4,z494,z13]),(0,[z7,z15,z2,z3,z466,z9]),(0,[z16,z7,z15,z345,z4,z13]),(0,[z7,z495,z159,z2,z4,z13])],[(0,[z16,z7,z15,z2,z222,z13]),(0,[z7,z15,z2,z3,z496,z4]),(0,[z7,z15,z2,z3,z4,z497])],[(0,[z249,z15,z355,z3,z4,z13]),(0,[z7,z15,z2,z4,z498,z13])],[(0,[z186,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z499,z4]),(0,[z70,z7,z15,z3,z4,z500]),(0,[z7,z15,z2,z32,z77,z9])]],
   [[(0,[z7,z15,z97,z3,z4,z13]),(0,[z501,z15,z2,z3,z4,z13])],[(0,[z129,z67,z15,z2,z4,z13]),(0,[z7,z15,z2,z28,z4,z77]),(0,[z7,z15,z210,z3,z168,z5]),(0,[z7,z15,z2,z267,z4,z13])],[(0,[z6,z7,z27,z8,z4,z13]),(0,[z7,z15,z2,z3,z4,z480])],[(0,[z252,z1,z2,z3,z4,z13]),(0,[z7,z15,z27,z2,z502,z13]),(0,[z7,z308,z2,z3,z4,z13]),(0,[z7,z15,z420,z2,z4,z9]),(0,[z503,z15,z2,z3,z32,z4])],[(0,[z53,z59,z2,z3,z84,z13])],[(0,[z16,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z504,z13]),(0,[z15,z2,z3,z4,z92,z218]),(0,[z16,z49,z15,z2,z50,z13]),(0,[z7,z15,z192,z193,z4,z9])],[(0,[z7,z63,z2,z300,z4,z13]),(0,[z7,z15,z27,z2,z505,z4]),(0,[z7,z15,z2,z32,z506,z4])],[(0,[z7,z15,z2,z3,z4,z35]),(0,[z507,z7,z15,z2,z3,z4]),(0,[z7,z48,z15,z2,z41,z9]),(0,[z46,z7,z2,z508,z4,z13])],[(0,[z10,z16,z15,z12,z4,z13]),(0,[z7,z15,z27,z2,z509,z13])],[(0,[z16,z7,z15,z2,z196,z4])],[(0,[z7,z15,z2,z510,z4,z13]),(0,[z70,z7,z15,z511,z3,z4])],[(0,[z0,z15,z2,z3,z4,z5])],[(0,[z7,z15,z2,z3,z4,z512]),(0,[z513,z15,z2,z3,z4,z13]),(0,[z15,z2,z3,z32,z366,z4])],[(0,[z16,z7,z2,z411,z4,z13]),(0,[z15,z2,z3,z168,z50,z5]),(0,[z7,z44,z2,z3,z4,z35])],[(0,[z10,z15,z27,z12,z4,z13]),(0,[z186,z15,z2,z3,z4,z5]),(0,[z15,z2,z3,z211,z4,z13])],[(0,[z7,z15,z97,z3,z4,z5]),(0,[z514,z7,z15,z57,z4,z13]),(0,[z16,z7,z15,z2,z4,z230]),(0,[z7,z241,z27,z2,z4,z13])],[(0,[z7,z15,z2,z229,z3,z35]),(0,[z7,z15,z2,z3,z4,z265]),(0,[z7,z515,z2,z3,z4,z9]),(0,[z516,z15,z2,z3,z21,z4])],[(0,[z6,z7,z8,z3,z4,z13]),(0,[z16,z7,z15,z2,z4,z212])],[(0,[z252,z1,z2,z3,z4,z5]),(0,[z7,z308,z2,z3,z4,z5])],[(0,[z7,z15,z345,z3,z4,z101])],[(0,[z0,z15,z2,z66,z4,z5]),(0,[z16,z7,z15,z2,z4,z5]),(0,[z25,z15,z2,z3,z4,z13])],[(0,[z10,z15,z517,z3,z4,z13]),(0,[z7,z15,z2,z4,z35,z518]),(0,[z16,z7,z2,z4,z519,z13])],[(0,[z7,z15,z2,z3,z4,z520]),(0,[z7,z15,z2,z4,z521,z13]),(0,[z7,z15,z2,z30,z4,z13])],[(0,[z522,z7,z15,z2,z4,z13]),(0,[z16,z7,z185,z2,z4,z13]),(0,[z16,z7,z2,z268,z4,z9]),(0,[z352,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z523,z4]),(0,[z15,z2,z524,z3,z4,z5]),(0,[z16,z0,z161,z2,z4,z13]),(0,[z7,z15,z2,z4,z5,z437]),(0,[z7,z15,z2,z525,z4,z13]),(0,[z7,z81,z241,z2,z4,z13]),(0,[z470,z15,z2,z3,z4,z13]),(0,[z16,z7,z15,z2,z526,z13]),(0,[z7,z48,z2,z295,z32,z4]),(0,[z7,z15,z2,z527,z4,z13]),(0,[z7,z15,z2,z528,z77,z13]),(0,[z15,z2,z3,z4,z529,z13]),(0,[z7,z15,z2,z3,z168,z218])],[(0,[z7,z15,z2,z510,z4,z5]),(0,[z7,z15,z2,z4,z77,z183]),(0,[z405,z7,z15,z317,z4,z13])],[(0,[z7,z15,z2,z248,z4,z35]),(0,[z86,z15,z2,z3,z21,z4]),(0,[z16,z7,z15,z2,z4,z198]),(0,[z530,z46,z7,z2,z4,z13]),(0,[z7,z15,z2,z531,z32,z4])],[(0,[z445,z7,z150,z2,z4,z13]),(0,[z7,z15,z532,z2,z4,z13]),(0,[z7,z15,z2,z3,z533,z4]),(0,[z15,z2,z3,z156,z50,z13]),(0,[z7,z15,z2,z534,z4,z13]),(0,[z7,z15,z2,z4,z77,z535])],[(0,[z7,z15,z2,z4,z536,z13]),(0,[z15,z537,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z508,z314])],[(0,[z7,z15,z2,z3,z538,z13]),(0,[z7,z15,z2,z539,z4,z13]),(1,[z7,z2,z267,z4,z13]),(0,[z7,z15,z2,z3,z540,z4]),(0,[z405,z7,z15,z4,z287,z13]),(0,[z7,z15,z122,z2,z32,z4])],[],[(0,[z7,z11,z2,z4,z77,z13]),(0,[z7,z15,z2,z3,z156,z42]),(0,[z7,z15,z2,z3,z4,z541]),(0,[z542,z7,z15,z2,z468,z4]),(0,[z70,z7,z15,z3,z121,z71])]],
   [[(0,[z6,z7,z8,z3,z4,z5]),(0,[z7,z15,z2,z297,z4,z35]),(0,[z7,z2,z180,z114,z77,z13]),(0,[z7,z15,z2,z131,z32,z4])],[(0,[z7,z15,z2,z543,z4,z13]),(0,[z7,z15,z2,z3,z4,z544])],[(0,[z139,z7,z2,z3,z32,z4]),(0,[z7,z15,z2,z4,z545,z9])],[(0,[z10,z15,z12,z3,z4,z151]),(0,[z7,z15,z2,z3,z96,z314]),(0,[z76,z7,z15,z2,z3,z215])],[(0,[z7,z15,z2,z4,z77,z33]),(0,[z7,z15,z2,z4,z88,z13]),(0,[z7,z15,z2,z3,z546,z9]),(0,[z7,z15,z2,z3,z4,z373])],[(0,[z137,z15,z138,z3,z4,z35]),(0,[z7,z270,z2,z3,z4,z35]),(0,[z7,z15,z27,z2,z4,z246])],[(0,[z7,z15,z2,z3,z143,z33]),(0,[z16,z7,z15,z2,z277,z13])],[(0,[z37,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z547,z4,z13])],[(0,[z7,z15,z548,z3,z4,z13]),(0,[z16,z7,z226,z2,z4,z22]),(0,[z59,z15,z2,z4,z77,z13])],[(0,[z7,z15,z2,z3,z4,z549])],[(0,[z129,z15,z2,z391,z4,z13]),(0,[z15,z2,z3,z156,z50,z5]),(0,[z7,z15,z2,z4,z284,z35]),(0,[z7,z15,z2,z3,z4,z550])],[],[(0,[z15,z2,z3,z156,z50,z4]),(0,[z7,z15,z2,z539,z4,z5]),(0,[z7,z15,z2,z551,z4,z13]),(0,[z7,z15,z192,z552,z4,z13])],[],[(0,[z91,z15,z2,z3,z92,z103]),(0,[z48,z15,z2,z3,z21,z4]),(0,[z46,z7,z2,z234,z4,z13])],[(0,[z15,z2,z553,z3,z4,z5]),(0,[z7,z15,z2,z3,z554,z13]),(0,[z175,z7,z44,z3,z41,z13])],[(0,[z7,z15,z2,z3,z4,z555]),(0,[z7,z15,z2,z3,z74,z13]),(0,[z7,z15,z2,z543,z4,z5]),(0,[z7,z15,z2,z3,z4,z556]),(0,[z7,z15,z2,z508,z419,z9])],[(0,[z7,z15,z2,z331,z41,z13]),(0,[z7,z15,z2,z123,z4,z13]),(0,[z203,z15,z2,z4,z77,z13])],[(0,[z7,z293,z2,z3,z4,z273]),(0,[z7,z110,z2,z557,z4,z13]),(0,[z7,z15,z2,z50,z331,z13]),(0,[z558,z7,z15,z2,z4,z559]),(0,[z7,z15,z2,z3,z4,z560]),(0,[z7,z15,z2,z561,z4,z13])],[(0,[z15,z2,z562,z3,z4,z5]),(0,[z313,z15,z12,z3,z4,z13]),(0,[z7,z15,z2,z4,z88,z5]),(0,[z7,z15,z2,z3,z563,z13]),(0,[z7,z15,z2,z384,z4,z77]),(0,[z564,z7,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z276,z13])],[(0,[z7,z15,z2,z3,z4,z565]),(0,[z7,z15,z2,z3,z4,z183]),(0,[z7,z15,z2,z3,z566,z9]),(0,[z7,z15,z2,z567,z4,z285])],[(0,[z7,z15,z2,z568,z77,z13]),(0,[z7,z15,z2,z136,z4,z13]),(0,[z7,z15,z192,z193,z32,z4]),(0,[z7,z15,z122,z2,z120,z4])],[(0,[z569,z7,z15,z2,z4,z13]),(0,[z7,z15,z97,z3,z4,z262]),(0,[z7,z15,z192,z317,z4,z13])],[(0,[z216,z15,z1,z2,z4,z5]),(0,[z7,z15,z2,z3,z4,z570]),(0,[z70,z7,z15,z3,z4,z71]),(0,[z7,z15,z27,z2,z215,z13])],[(0,[z7,z15,z2,z3,z571,z13]),(0,[z137,z15,z2,z3,z21,z4]),(0,[z7,z572,z15,z2,z4,z13]),(0,[z7,z15,z2,z180,z276,z13]),(0,[z7,z327,z2,z4,z77,z13]),(0,[z573,z7,z15,z2,z4,z13])],[],[(0,[z7,z11,z2,z3,z4,z13]),(0,[z416,z15,z2,z3,z4,z262]),(0,[z15,z2,z3,z4,z218,z42]),(0,[z76,z7,z308,z2,z3,z4]),(0,[z7,z574,z2,z3,z32,z4])],[(0,[z7,z15,z2,z3,z575,z4]),(0,[z16,z7,z15,z2,z4,z262]),(0,[z7,z15,z2,z551,z4,z5]),(0,[z576,z15,z27,z2,z4,z13])],[(0,[z7,z185,z2,z4,z77,z13]),(0,[z7,z15,z2,z208,z32,z4])],[(0,[z7,z15,z517,z3,z4,z13]),(0,[z16,z7,z15,z2,z4,z266]),(0,[z577,z7,z15,z2,z4,z13]),(0,[z7,z15,z578,z3,z168,z13]),(0,[z374,z7,z2,z3,z4,z579])],[(0,[z7,z15,z2,z3,z580,z4])],[(0,[z7,z15,z2,z3,z4,z33]),(0,[z581,z7,z15,z3,z41,z13]),(0,[z46,z7,z2,z193,z4,z13]),(0,[z46,z582,z7,z2,z4,z13])]],
   [[(0,[z216,z7,z15,z2,z32,z4]),(0,[z7,z110,z2,z4,z77,z13]),(0,[z7,z15,z2,z77,z13,z314]),(0,[z53,z16,z7,z2,z95,z13]),(0,[z16,z133,z15,z2,z4,z13]),(0,[z583,z7,z48,z2,z4,z13]),(0,[z7,z584,z2,z3,z4,z13])],[(0,[z7,z585,z15,z2,z4,z13]),(0,[z7,z15,z345,z4,z77,z13]),(0,[z7,z15,z586,z2,z4,z13]),(0,[z15,z2,z3,z587,z4,z13])],[(0,[z7,z15,z588,z2,z4,z13]),(0,[z46,z7,z589,z2,z4,z13]),(0,[z16,z7,z15,z2,z384,z4])],[(0,[z15,z2,z3,z590,z4,z13]),(0,[z15,z591,z2,z3,z21,z4])],[(0,[z7,z15,z2,z592,z4,z13]),(0,[z16,z7,z150,z2,z4,z13]),(0,[z46,z7,z2,z4,z593,z13])],[],[(0,[z7,z15,z2,z3,z4,z594]),(0,[z7,z62,z15,z2,z4,z13]),(0,[z16,z7,z159,z2,z4,z13])],[(0,[z7,z15,z2,z595,z4,z13]),(0,[z7,z15,z2,z3,z596,z4]),(0,[z91,z15,z149,z3,z92,z13]),(0,[z7,z15,z2,z3,z597,z13])],[(0,[z6,z7,z598,z8,z3,z4])],[(0,[z7,z15,z2,z3,z4,z599]),(0,[z7,z11,z2,z3,z4,z5]),(0,[z70,z7,z185,z3,z4,z71]),(0,[z7,z15,z2,z180,z77,z9])],[(0,[z7,z15,z2,z3,z600,z4]),(0,[z91,z48,z15,z2,z4,z5])],[(0,[z7,z15,z2,z3,z4,z601]),(0,[z133,z15,z27,z2,z4,z13])],[(0,[z203,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z156,z4]),(0,[z7,z15,z2,z4,z34,z5])],[(0,[z7,z15,z2,z602,z4,z13]),(0,[z7,z241,z2,z3,z32,z4])],[(0,[z10,z46,z7,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z603]),(0,[z7,z48,z15,z2,z4,z103]),(0,[z7,z15,z2,z32,z4,z351]),(0,[z6,z15,z2,z3,z21,z4]),(0,[z7,z48,z15,z2,z4,z119]),(0,[z203,z15,z2,z3,z4,z24])],[(0,[z7,z15,z2,z3,z604,z4]),(0,[z249,z15,z2,z3,z32,z4]),(0,[z7,z15,z2,z3,z4,z398]),(0,[z7,z15,z605,z2,z4,z13])],[(0,[z16,z7,z2,z606,z4,z13]),(0,[z7,z607,z2,z3,z4,z13]),(0,[z608,z15,z2,z3,z4,z13]),(0,[z16,z7,z48,z2,z4,z13]),(0,[z16,z7,z15,z2,z508,z9]),(0,[z7,z15,z2,z100,z4,z9]),(0,[z7,z15,z2,z3,z443,z9])],[(0,[z7,z15,z2,z3,z4,z609]),(0,[z7,z412,z15,z2,z4,z13])],[(0,[z16,z1,z2,z3,z4,z5]),(0,[z7,z610,z2,z3,z4,z13]),(0,[z7,z15,z2,z255,z32,z4]),(0,[z46,z7,z2,z95,z4,z13]),(0,[z203,z44,z2,z3,z4,z13]),(0,[z7,z15,z611,z2,z121,z13])],[(0,[z612,z7,z15,z2,z3,z4]),(0,[z7,z15,z2,z3,z4,z613]),(0,[z7,z15,z2,z3,z32,z314]),(0,[z7,z15,z2,z3,z614,z4]),(0,[z46,z7,z2,z32,z4,z77])],[(0,[z7,z15,z2,z3,z615,z9]),(0,[z7,z15,z2,z616,z4,z13]),(0,[z304,z15,z2,z3,z4,z617])],[(0,[z16,z618,z7,z2,z4,z13]),(0,[z16,z7,z94,z2,z95,z13]),(0,[z7,z15,z2,z3,z111,z13])],[(0,[z7,z15,z2,z3,z597,z5])],[(0,[z619,z7,z110,z2,z4,z13]),(0,[z542,z7,z15,z192,z193,z4])],[(0,[z7,z15,z2,z3,z4,z119]),(0,[z7,z15,z2,z620,z4,z13]),(0,[z7,z15,z2,z3,z4,z621])],[(0,[z1,z2,z3,z4,z84,z5]),(0,[z7,z150,z2,z3,z4,z35]),(0,[z16,z7,z2,z622,z4,z13]),(0,[z304,z15,z27,z2,z4,z13])],[(0,[z237,z15,z2,z3,z4,z13]),(0,[z16,z7,z15,z2,z4,z341])],[(0,[z15,z2,z3,z4,z324,z5]),(0,[z203,z15,z2,z3,z4,z5])],[(0,[z7,z15,z2,z372,z4,z151]),(0,[z7,z15,z387,z2,z4,z35]),(0,[z46,z7,z148,z2,z4,z13]),(0,[z7,z15,z2,z623,z4,z13]),(0,[z7,z15,z2,z118,z4,z624])],[(0,[z15,z2,z12,z3,z21,z4]),(0,[z48,z15,z625,z2,z4,z5]),(0,[z7,z15,z2,z4,z13,z626]),(0,[z627,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z4,z628,z13]),(0,[z7,z15,z2,z4,z13,z166]),(0,[z7,z2,z4,z77,z13,z629]),(0,[z15,z2,z3,z32,z590,z4])],[(0,[z54,z7,z1,z2,z4,z13]),(0,[z7,z15,z2,z510,z4,z341]),(0,[z16,z7,z48,z2,z4,z5])]],
   [[(0,[z7,z412,z15,z2,z4,z5]),(0,[z630,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z77,z41,z9])],[],[(0,[z7,z15,z2,z3,z4,z631]),(0,[z7,z63,z2,z4,z77,z13])],[(0,[z53,z16,z7,z2,z4,z101]),(0,[z304,z15,z2,z3,z215,z13])],[(0,[z7,z15,z2,z4,z351,z52]),(0,[z7,z135,z2,z3,z4,z35])],[(0,[z7,z15,z2,z3,z4,z632]),(0,[z7,z15,z2,z276,z4,z13])],[(0,[z7,z15,z2,z3,z4,z633]),(0,[z7,z15,z2,z3,z4,z634]),(0,[z7,z15,z2,z3,z4,z635])],[(0,[z15,z2,z12,z3,z4,z183]),(0,[z636,z7,z15,z2,z3,z4]),(0,[z16,z7,z261,z2,z32,z4]),(0,[z7,z15,z178,z193,z4,z13])],[(0,[z7,z15,z2,z3,z637,z13]),(0,[z7,z15,z2,z3,z4,z474]),(0,[z16,z7,z412,z2,z4,z13]),(0,[z7,z15,z27,z2,z638,z13])],[],[(0,[z7,z15,z2,z3,z639,z4]),(0,[z7,z15,z2,z3,z4,z324]),(0,[z7,z15,z2,z3,z215,z160]),(0,[z7,z15,z611,z2,z4,z13])],[],[(0,[z7,z15,z2,z300,z32,z4]),(0,[z7,z159,z2,z3,z4,z35]),(0,[z7,z15,z640,z2,z4,z13])],[(0,[z7,z15,z641,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z40]),(0,[z7,z94,z2,z95,z88,z13]),(0,[z7,z15,z27,z2,z305,z4]),(0,[z7,z2,z4,z642,z77,z13]),(0,[z15,z2,z3,z21,z4,z77]),(0,[z15,z27,z2,z21,z4,z13])],[(0,[z643,z1,z2,z3,z4,z13]),(0,[z644,z15,z2,z3,z4,z5]),(0,[z91,z15,z2,z3,z32,z92])],[(0,[z7,z15,z645,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z646]),(0,[z15,z1,z2,z3,z4,z5]),(0,[z10,z15,z12,z4,z77,z13]),(0,[z647,z7,z15,z2,z4,z13]),(0,[z53,z7,z2,z3,z84,z5])],[(0,[z7,z15,z149,z3,z4,z13]),(0,[z256,z15,z2,z4,z47,z13]),(0,[z648,z7,z15,z2,z3,z4]),(0,[z7,z15,z2,z3,z4,z649]),(0,[z7,z15,z650,z4,z77,z160]),(0,[z15,z2,z3,z21,z508,z4])],[(0,[z16,z7,z328,z2,z4,z13]),(0,[z651,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z32,z652]),(0,[z7,z15,z2,z3,z4,z653]),(0,[z7,z48,z15,z2,z4,z654])],[(0,[z7,z15,z2,z3,z4,z655]),(0,[z656,z7,z15,z3,z489,z4])],[(0,[z16,z7,z15,z2,z4,z383]),(0,[z7,z15,z2,z3,z4,z657]),(0,[z658,z7,z15,z2,z4,z659]),(0,[z15,z2,z3,z21,z4,z187])],[(0,[z91,z16,z15,z2,z92,z13])],[(0,[z16,z7,z15,z2,z4,z189]),(0,[z7,z15,z2,z660,z4,z13]),(0,[z16,z7,z2,z661,z4,z13])],[(0,[z390,z7,z2,z8,z4,z13]),(0,[z7,z15,z2,z662,z385,z4])],[(0,[z15,z2,z3,z663,z50,z5]),(0,[z7,z15,z2,z664,z4,z13]),(0,[z15,z2,z3,z21,z96,z4]),(0,[z15,z2,z3,z21,z4,z9])],[(0,[z16,z665,z7,z2,z4,z13]),(0,[z7,z37,z15,z3,z41,z13]),(0,[z7,z666,z2,z4,z77,z13])],[(0,[z16,z7,z2,z4,z667,z13]),(0,[z7,z2,z3,z32,z668,z4])],[(0,[z91,z15,z27,z2,z92,z13]),(0,[z7,z15,z2,z3,z4,z669]),(0,[z7,z15,z2,z100,z4,z119]),(0,[z670,z7,z2,z3,z4,z13])],[(0,[z10,z48,z15,z12,z4,z13]),(0,[z16,z7,z15,z2,z4,z401]),(0,[z7,z15,z2,z3,z4,z654]),(0,[z16,z7,z625,z2,z4,z13]),(0,[z7,z48,z15,z2,z4,z671])],[(0,[z7,z63,z2,z3,z4,z13]),(0,[z7,z15,z2,z672,z4,z13]),(0,[z405,z7,z15,z58,z4,z9]),(0,[z46,z7,z673,z2,z4,z13]),(0,[z7,z15,z51,z2,z4,z9])],[(0,[z7,z15,z2,z3,z4,z674]),(0,[z675,z15,z2,z3,z4,z13])],[(0,[z7,z471,z1,z2,z4,z13]),(0,[z15,z2,z12,z3,z156,z4]),(0,[z676,z7,z15,z677,z4,z13])]],
   [[(0,[z7,z15,z149,z3,z4,z5]),(0,[z15,z27,z2,z50,z4,z5]),(0,[z416,z15,z2,z3,z4,z218]),(0,[z7,z48,z2,z678,z4,z13]),(0,[z7,z679,z2,z3,z4,z13])],[(0,[z7,z15,z2,z440,z4,z35]),(0,[z680,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z681,z4,z13]),(0,[z7,z15,z2,z3,z4,z682])],[(0,[z7,z15,z27,z2,z120,z4])],[(0,[z53,z7,z2,z100,z84,z13])],[(0,[z7,z15,z2,z4,z683,z13]),(0,[z7,z15,z684,z2,z4,z13]),(0,[z7,z15,z2,z453,z4,z35]),(0,[z7,z15,z2,z685,z4,z13]),(0,[z175,z7,z135,z3,z41,z13]),(0,[z7,z15,z2,z686,z4,z13]),(0,[z687,z15,z2,z3,z4,z13])],[(0,[z7,z15,z81,z2,z4,z9])],[(0,[z16,z7,z15,z2,z4,z456]),(0,[z16,z7,z15,z2,z32,z9]),(0,[z688,z15,z2,z3,z4,z13])],[(0,[z46,z161,z7,z2,z4,z13]),(0,[z689,z7,z2,z3,z4,z13]),(0,[z7,z48,z135,z2,z4,z13]),(0,[z7,z15,z2,z3,z690,z9]),(0,[z46,z7,z2,z4,z77,z9])],[(0,[z186,z15,z2,z468,z4,z13]),(0,[z274,z7,z15,z2,z3,z215]),(0,[z133,z15,z2,z3,z32,z4])],[(0,[z7,z15,z2,z557,z4,z9]),(0,[z7,z15,z2,z3,z4,z691]),(0,[z16,z692,z15,z2,z4,z13]),(0,[z7,z693,z15,z2,z4,z13]),(0,[z54,z46,z7,z2,z4,z13])],[(0,[z7,z15,z223,z2,z4,z52]),(0,[z7,z15,z2,z379,z32,z4])],[(0,[z7,z15,z27,z2,z143,z13]),(0,[z16,z7,z2,z8,z4,z13]),(0,[z7,z694,z2,z3,z4,z13]),(0,[z304,z15,z2,z3,z4,z160]),(0,[z7,z15,z2,z4,z77,z695])],[(0,[z46,z7,z2,z155,z4,z13]),(0,[z7,z15,z2,z343,z4,z35]),(0,[z7,z308,z2,z468,z4,z13]),(0,[z7,z15,z27,z2,z121,z13])],[],[(0,[z7,z15,z696,z3,z4,z13]),(0,[z7,z15,z2,z697,z4,z13]),(0,[z7,z15,z698,z2,z222,z13]),(0,[z7,z15,z2,z4,z351,z13]),(0,[z416,z15,z2,z3,z244,z4]),(0,[z7,z15,z2,z699,z4,z13])],[(0,[z16,z161,z7,z2,z32,z4]),(0,[z256,z15,z2,z141,z4,z13]),(0,[z16,z7,z15,z2,z244,z4]),(0,[z416,z15,z2,z4,z77,z35]),(0,[z54,z7,z2,z8,z4,z13]),(0,[z16,z7,z700,z2,z4,z13])],[(0,[z7,z150,z2,z3,z4,z33]),(0,[z7,z15,z2,z468,z4,z35]),(0,[z16,z7,z495,z2,z4,z13]),(0,[z76,z7,z27,z2,z4,z78]),(0,[z274,z7,z15,z2,z468,z4])],[(0,[z16,z7,z701,z2,z4,z13]),(0,[z7,z15,z355,z3,z4,z13]),(0,[z7,z15,z2,z3,z702,z4]),(0,[z7,z15,z2,z221,z77,z13])],[(0,[z7,z148,z15,z2,z4,z35]),(0,[z16,z7,z15,z2,z703,z4]),(0,[z7,z48,z15,z2,z4,z246])],[(0,[z7,z15,z2,z3,z4,z704]),(0,[z705,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z706,z4]),(0,[z7,z15,z707,z3,z4,z13]),(0,[z542,z7,z15,z2,z4,z77])],[(0,[z7,z15,z2,z708,z4,z13]),(0,[z7,z15,z2,z709,z4,z13]),(0,[z16,z15,z2,z4,z35,z5]),(0,[z7,z241,z2,z3,z4,z5]),(0,[z304,z226,z15,z2,z3,z4]),(0,[z7,z15,z3,z168,z214,z13])],[(0,[z710,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z711]),(0,[z7,z15,z2,z34,z77,z13]),(0,[z304,z15,z2,z3,z32,z4])],[(0,[z712,z7,z2,z3,z4,z13]),(0,[z7,z94,z15,z2,z3,z314]),(0,[z7,z226,z2,z3,z4,z713]),(0,[z7,z714,z15,z2,z4,z13]),(0,[z7,z15,z2,z4,z77,z9]),(0,[z7,z15,z2,z3,z336,z508])],[(0,[z7,z15,z210,z3,z168,z35])],[(0,[z16,z7,z15,z2,z4,z439]),(0,[z715,z15,z2,z3,z4,z5]),(0,[z6,z46,z7,z2,z4,z13])],[(0,[z49,z15,z2,z3,z50,z52]),(0,[z15,z2,z716,z3,z4,z5]),(0,[z7,z15,z2,z3,z4,z717])],[(0,[z7,z15,z27,z345,z4,z13])],[(0,[z7,z15,z27,z2,z222,z13]),(0,[z7,z718,z2,z3,z4,z13]),(0,[z7,z293,z2,z4,z77,z13]),(0,[z7,z15,z2,z4,z5,z166]),(0,[z16,z7,z2,z4,z719,z13]),(0,[z7,z15,z2,z3,z32,z336]),(0,[z720,z15,z2,z3,z21,z4])],[(0,[z7,z15,z2,z3,z4,z721]),(0,[z7,z15,z2,z4,z351,z5]),(0,[z7,z15,z2,z3,z4,z722]),(0,[z53,z7,z2,z3,z84,z101])],[(0,[z256,z15,z2,z141,z4,z5]),(0,[z7,z15,z2,z723,z4,z13]),(0,[z724,z15,z2,z3,z4,z5]),(0,[z725,z7,z2,z4,z77,z13])]],
   [[(0,[z7,z726,z2,z3,z4,z13]),(0,[z727,z15,z2,z155,z4,z13]),(0,[z7,z15,z2,z3,z490,z35]),(0,[z728,z7,z8,z3,z4,z13]),(0,[z7,z15,z2,z3,z729,z9])],[(0,[z7,z15,z730,z3,z4,z13]),(0,[z15,z2,z3,z4,z13,z520]),(0,[z7,z15,z355,z3,z4,z5]),(0,[z7,z15,z2,z3,z4,z731]),(0,[z7,z15,z2,z3,z4,z732])],[(0,[z733,z15,z2,z3,z4,z13]),(0,[z15,z2,z3,z21,z275,z4])],[(0,[z7,z15,z27,z2,z734,z13]),(0,[z46,z7,z2,z3,z4,z9])],[(0,[z15,z2,z3,z735,z4,z5])],[(0,[z7,z15,z27,z2,z4,z13]),(0,[z175,z16,z7,z15,z41,z13]),(0,[z7,z48,z15,z2,z215,z13]),(0,[z7,z15,z736,z2,z4,z13]),(0,[z46,z7,z2,z168,z4,z13])],[(0,[z15,z2,z3,z4,z5,z218]),(0,[z186,z15,z2,z3,z4,z35]),(0,[z225,z7,z15,z27,z2,z4])],[(0,[z7,z737,z2,z3,z4,z13]),(0,[z7,z15,z149,z3,z4,z262]),(0,[z7,z15,z97,z3,z4,z35]),(0,[z7,z94,z2,z3,z95,z55]),(0,[z7,z15,z2,z3,z362,z4])],[(0,[z738,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z739,z4]),(0,[z530,z7,z15,z2,z34,z13]),(0,[z7,z2,z3,z4,z740,z13])],[(0,[z16,z161,z67,z2,z4,z13]),(0,[z7,z15,z210,z3,z741,z13]),(0,[z576,z48,z15,z2,z4,z13]),(0,[z203,z135,z2,z3,z4,z13])],[(0,[z252,z1,z2,z3,z4,z35]),(0,[z7,z15,z2,z3,z4,z742]),(0,[z7,z308,z2,z3,z4,z35]),(0,[z16,z7,z15,z355,z4,z13])],[(0,[z743,z15,z12,z3,z4,z13]),(0,[z416,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z744,z3,z4])],[(0,[z16,z7,z15,z2,z4,z35]),(0,[z249,z15,z2,z100,z4,z13]),(0,[z7,z745,z2,z3,z4,z13]),(0,[z46,z7,z27,z2,z77,z13])],[],[(0,[z7,z48,z241,z2,z4,z13])],[(0,[z7,z15,z2,z3,z156,z92]),(0,[z7,z15,z2,z3,z35,z746]),(0,[z16,z7,z2,z747,z4,z13]),(0,[z7,z15,z2,z748,z4,z13]),(0,[z7,z15,z2,z3,z215,z13])],[(0,[z7,z15,z2,z749,z4,z13]),(0,[z530,z16,z7,z2,z4,z13]),(0,[z750,z7,z15,z2,z4,z13])],[(0,[z7,z15,z2,z510,z4,z35]),(0,[z91,z15,z2,z557,z4,z5]),(0,[z7,z264,z15,z2,z3,z4]),(0,[z7,z15,z27,z2,z4,z212])],[(0,[z576,z15,z2,z3,z4,z22]),(0,[z7,z15,z27,z2,z196,z96])],[(0,[z576,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z751,z4,z13]),(0,[z7,z15,z2,z752,z143,z13]),(0,[z7,z15,z2,z244,z4,z351]),(0,[z7,z15,z27,z2,z4,z5]),(0,[z75,z15,z2,z3,z32,z4])],[(0,[z0,z15,z2,z510,z4,z5]),(0,[z7,z15,z2,z557,z4,z103]),(0,[z7,z15,z2,z3,z77,z314]),(0,[z7,z86,z753,z3,z4,z13]),(0,[z7,z15,z2,z754,z3,z32]),(0,[z7,z15,z2,z234,z32,z77])],[(0,[z7,z15,z81,z2,z32,z4])],[(0,[z7,z1,z2,z4,z331,z13]),(0,[z7,z15,z755,z3,z4,z13]),(0,[z15,z2,z3,z4,z35,z756]),(0,[z7,z495,z15,z757,z4,z13]),(1,[z46,z7,z2,z4,z9])],[(0,[z7,z15,z2,z758,z4,z13]),(0,[z558,z7,z15,z2,z4,z79]),(0,[z6,z7,z8,z3,z4,z35]),(0,[z7,z15,z2,z759,z4,z13]),(0,[z760,z7,z15,z3,z4,z761])],[(0,[z16,z7,z2,z267,z4,z13]),(0,[z133,z48,z15,z2,z4,z13]),(0,[z304,z15,z2,z3,z121,z13]),(0,[z46,z762,z7,z2,z4,z13])],[(0,[z7,z15,z763,z3,z4,z13]),(0,[z7,z764,z2,z3,z4,z13]),(0,[z416,z15,z2,z3,z4,z520]),(0,[z7,z15,z27,z2,z4,z198])],[],[(0,[z7,z15,z2,z66,z4,z9]),(0,[z390,z7,z86,z2,z4,z13]),(0,[z7,z15,z27,z2,z77,z13])],[(0,[z7,z15,z27,z97,z4,z13]),(0,[z7,z15,z418,z2,z4,z13]),(0,[z70,z7,z48,z15,z4,z71]),(0,[z70,z7,z15,z343,z4,z71]),(0,[z7,z15,z2,z4,z419,z13])],[(0,[z7,z15,z2,z3,z215,z5]),(0,[z7,z2,z8,z4,z331,z13]),(0,[z765,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z766,z9]),(0,[z15,z2,z3,z21,z489,z4])],[(0,[z16,z7,z767,z2,z4,z13]),(1,[z15,z2,z3,z587,z4]),(0,[z233,z15,z2,z3,z4,z9])]],
   [[(0,[z7,z768,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z769,z13]),(0,[z16,z7,z15,z2,z770,z13]),(0,[z771,z15,z2,z3,z4,z13]),(0,[z772,z46,z7,z2,z4,z13]),(0,[z46,z7,z2,z4,z773,z13])],[(0,[z70,z7,z15,z468,z4,z71])],[(0,[z7,z15,z774,z3,z4,z13]),(0,[z576,z15,z2,z3,z4,z5]),(0,[z7,z15,z775,z193,z4,z13]),(0,[z7,z15,z2,z776,z77,z13]),(0,[z7,z15,z2,z3,z4,z777])],[(0,[z7,z778,z2,z3,z4,z13]),(0,[z46,z7,z2,z4,z13,z5]),(0,[z503,z15,z2,z3,z4,z13]),(0,[z7,z779,z15,z2,z4,z13])],[(0,[z7,z15,z2,z372,z4,z13]),(0,[z7,z15,z2,z3,z538,z35]),(0,[z7,z15,z2,z598,z4,z77]),(0,[z7,z15,z269,z2,z4,z780])],[(0,[z7,z15,z2,z752,z222,z13]),(0,[z15,z138,z2,z3,z21,z4])],[(0,[z249,z15,z2,z3,z4,z101]),(0,[z7,z15,z2,z84,z77,z9])],[(0,[z7,z109,z15,z2,z4,z13]),(0,[z304,z48,z15,z2,z4,z13])],[(0,[z781,z7,z15,z3,z4,z71]),(0,[z7,z2,z3,z563,z84,z13])],[(0,[z7,z15,z2,z244,z4,z77]),(0,[z15,z2,z3,z32,z21,z4])],[(0,[z7,z15,z2,z4,z782,z13]),(0,[z7,z15,z2,z143,z783,z13]),(0,[z7,z15,z2,z3,z4,z784]),(0,[z7,z15,z785,z193,z4,z13]),(0,[z203,z15,z2,z453,z4,z13])],[(0,[z7,z15,z2,z4,z88,z35]),(0,[z113,z15,z2,z3,z4,z9])],[(0,[z7,z15,z2,z3,z4,z786]),(0,[z7,z2,z3,z4,z787,z13]),(0,[z7,z15,z418,z2,z4,z5]),(0,[z7,z15,z2,z4,z419,z5]),(0,[z15,z2,z3,z4,z35,z788]),(0,[z7,z15,z2,z297,z4,z9]),(0,[z46,z274,z7,z2,z4,z13])],[(0,[z7,z15,z2,z752,z4,z13]),(0,[z7,z789,z2,z4,z77,z13])],[(0,[z129,z15,z2,z155,z32,z4]),(0,[z7,z15,z149,z557,z4,z13]),(0,[z7,z48,z15,z2,z4,z790])],[(0,[z791,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z4,z792,z13]),(0,[z7,z15,z2,z3,z769,z5]),(0,[z793,z7,z15,z87,z4,z13]),(0,[z16,z7,z15,z2,z21,z4])],[(0,[z0,z15,z2,z3,z4,z183]),(0,[z137,z15,z12,z3,z4,z5])],[(0,[z7,z794,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z795,z4]),(0,[z16,z7,z86,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z796]),(0,[z15,z2,z3,z797,z4,z13])],[(0,[z133,z15,z2,z3,z4,z5])],[(0,[z7,z15,z2,z3,z4,z798]),(0,[z7,z15,z2,z372,z4,z5]),(0,[z37,z15,z2,z3,z4,z9]),(0,[z175,z7,z15,z3,z32,z41]),(0,[z7,z15,z2,z3,z4,z799]),(0,[z46,z7,z2,z3,z32,z4])],[(0,[z800,z15,z2,z3,z4,z5])],[],[(0,[z7,z15,z2,z4,z284,z9])],[(0,[z49,z15,z2,z50,z77,z13])],[(0,[z15,z138,z517,z3,z4,z13]),(0,[z7,z48,z2,z295,z4,z13]),(0,[z7,z15,z2,z3,z4,z790])],[(0,[z16,z7,z15,z2,z4,z183]),(0,[z90,z15,z2,z4,z77,z5]),(0,[z15,z2,z3,z801,z4,z5]),(0,[z7,z15,z2,z253,z77,z13]),(0,[z15,z802,z2,z3,z21,z4])],[(0,[z226,z15,z2,z3,z21,z4])],[(0,[z7,z48,z15,z2,z4,z40]),(0,[z7,z15,z27,z2,z4,z262]),(0,[z7,z48,z15,z2,z305,z4])],[(0,[z7,z15,z2,z752,z4,z5]),(0,[z7,z15,z2,z568,z77,z35])],[(0,[z7,z15,z27,z2,z4,z266]),(0,[z7,z15,z589,z3,z41,z9])],[],[(0,[z49,z15,z2,z3,z361,z13]),(0,[z7,z15,z2,z4,z803,z13]),(0,[z7,z15,z2,z3,z804,z4]),(0,[z49,z15,z2,z3,z32,z50]),(0,[z16,z805,z7,z2,z4,z13]),(0,[z16,z7,z15,z696,z4,z13]),(0,[z53,z16,z249,z2,z4,z13]),(0,[z7,z15,z2,z23,z4,z13]),(0,[z806,z15,z2,z3,z4,z13])]],
   [[(0,[z304,z15,z2,z3,z4,z5]),(0,[z7,z807,z2,z3,z4,z13])],[(0,[z7,z11,z2,z3,z4,z35]),(0,[z7,z48,z2,z808,z4,z13]),(0,[z16,z7,z44,z2,z4,z13]),(0,[z15,z2,z3,z809,z21,z4])],[(0,[z7,z15,z2,z3,z4,z810]),(0,[z16,z7,z210,z8,z4,z13]),(0,[z7,z2,z95,z4,z811,z13]),(0,[z7,z15,z2,z32,z4,z34]),(0,[z812,z15,z2,z3,z4,z13]),(0,[z7,z15,z27,z2,z384,z4]),(0,[z70,z15,z2,z3,z21,z4])],[(0,[z7,z15,z2,z3,z32,z4]),(0,[z7,z15,z813,z3,z4,z13]),(0,[z7,z15,z2,z814,z3,z4])],[(0,[z16,z7,z15,z2,z4,z33]),(0,[z7,z15,z2,z3,z4,z815]),(0,[z16,z7,z2,z816,z4,z13])],[(0,[z7,z15,z2,z817,z4,z13]),(0,[z7,z15,z2,z3,z305,z4]),(0,[z7,z15,z2,z3,z32,z121])],[(0,[z665,z1,z2,z3,z4,z13]),(0,[z7,z818,z2,z3,z4,z13]),(0,[z819,z7,z15,z2,z4,z13])],[(0,[z820,z7,z15,z2,z3,z4]),(0,[z46,z7,z650,z2,z4,z13])],[(0,[z0,z15,z2,z3,z156,z4]),(0,[z49,z15,z2,z3,z21,z4]),(0,[z7,z15,z2,z3,z4,z821]),(0,[z16,z7,z2,z822,z4,z13])],[(0,[z91,z48,z15,z2,z92,z13]),(0,[z7,z823,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z824,z4]),(0,[z16,z7,z308,z2,z4,z13]),(0,[z7,z44,z2,z3,z32,z4]),(0,[z7,z15,z2,z3,z4,z309]),(0,[z15,z2,z3,z21,z177,z4])],[(0,[z825,z15,z2,z141,z4,z13])],[(0,[z7,z15,z27,z2,z96,z695])],[(1,[z7,z15,z2,z331,z9])],[(0,[z7,z15,z2,z3,z4,z826])],[(0,[z7,z15,z2,z3,z143,z152]),(0,[z7,z15,z2,z23,z4,z5]),(0,[z7,z15,z650,z827,z3,z4])],[(0,[z7,z15,z2,z828,z4,z13]),(0,[z7,z15,z829,z2,z4,z13]),(0,[z16,z7,z2,z95,z4,z55]),(0,[z7,z15,z27,z2,z830,z13])],[(0,[z7,z48,z86,z589,z4,z13]),(0,[z7,z15,z2,z118,z4,z831]),(0,[z832,z15,z2,z3,z4,z13]),(0,[z7,z15,z27,z2,z508,z9]),(0,[z7,z15,z2,z4,z9,z833]),(0,[z834,z15,z2,z3,z21,z4])],[(0,[z16,z7,z15,z2,z156,z4]),(0,[z7,z48,z15,z2,z120,z4])],[(0,[z15,z2,z3,z4,z262,z5]),(0,[z835,z7,z15,z2,z4,z13]),(1,[z7,z15,z2,z4,z309])],[(0,[z203,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z331,z13,z9]),(0,[z7,z15,z420,z2,z4,z13])],[(0,[z16,z161,z147,z2,z4,z13]),(0,[z90,z15,z2,z3,z4,z5]),(0,[z249,z15,z2,z4,z77,z13]),(0,[z836,z7,z15,z58,z4,z13]),(0,[z837,z7,z2,z4,z77,z13])],[(0,[z15,z27,z2,z4,z35,z5]),(0,[z16,z147,z15,z2,z4,z5]),(0,[z16,z7,z2,z4,z811,z13])],[(0,[z7,z15,z838,z2,z4,z13]),(0,[z186,z185,z2,z3,z4,z13])],[(0,[z7,z15,z2,z4,z77,z205]),(0,[z7,z150,z27,z2,z4,z13]),(0,[z7,z839,z2,z3,z4,z13]),(0,[z16,z7,z48,z2,z4,z35]),(0,[z840,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z32,z297,z4]),(0,[z7,z15,z27,z2,z96,z9])],[(0,[z7,z412,z15,z2,z4,z35]),(0,[z7,z15,z2,z841,z4,z13]),(0,[z7,z15,z2,z3,z32,z842]),(0,[z7,z15,z2,z3,z843,z9])],[(0,[z7,z15,z2,z844,z77,z13]),(0,[z133,z15,z2,z3,z4,z262]),(0,[z7,z2,z290,z8,z4,z13]),(0,[z7,z15,z2,z845,z4,z13])],[(0,[z7,z15,z27,z2,z4,z341]),(0,[z7,z15,z2,z3,z4,z846]),(0,[z7,z48,z15,z2,z143,z13]),(0,[z7,z15,z2,z3,z847,z9]),(0,[z7,z15,z2,z505,z3,z4])],[(0,[z7,z15,z848,z3,z4,z13]),(0,[z7,z15,z2,z331,z92,z13]),(0,[z7,z48,z15,z2,z121,z13]),(0,[z7,z15,z2,z3,z120,z4])],[(0,[z1,z2,z3,z4,z481,z13]),(0,[z7,z15,z2,z3,z428,z4]),(0,[z7,z15,z2,z849,z4,z13]),(0,[z16,z7,z850,z2,z4,z13]),(0,[z7,z15,z2,z851,z4,z13])],[(0,[z7,z15,z2,z852,z4,z13]),(0,[z7,z15,z2,z3,z4,z853])],[(0,[z854,z7,z15,z2,z4,z13]),(0,[z76,z7,z2,z3,z4,z191])],[(0,[z256,z15,z2,z141,z4,z383]),(0,[z7,z15,z2,z3,z4,z855]),(0,[z16,z7,z2,z856,z4,z13])]],
   [[(0,[z225,z7,z15,z2,z3,z4]),(0,[z7,z15,z2,z4,z857,z13]),(0,[z16,z249,z15,z2,z4,z13]),(0,[z7,z48,z15,z813,z4,z13]),(0,[z7,z515,z2,z3,z4,z13])],[(0,[z216,z7,z2,z8,z4,z13])],[(0,[z237,z7,z2,z3,z4,z13]),(0,[z7,z15,z2,z4,z77,z273]),(0,[z91,z15,z2,z3,z92,z5]),(0,[z7,z15,z420,z2,z4,z5]),(0,[z760,z7,z15,z3,z41,z9])],[(0,[z7,z15,z2,z3,z4,z858]),(0,[z7,z94,z2,z3,z859,z13]),(0,[z37,z15,z2,z3,z32,z4])],[],[(0,[z860,z15,z2,z3,z4,z35])],[(0,[z7,z2,z209,z3,z4,z13]),(0,[z861,z15,z2,z3,z4,z13])],[(0,[z16,z7,z2,z268,z4,z13])],[(0,[z7,z15,z2,z3,z862,z9]),(0,[z7,z15,z863,z3,z4,z13]),(0,[z7,z864,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z865]),(0,[z76,z7,z2,z3,z4,z116]),(0,[z405,z7,z241,z58,z4,z13])],[(0,[z7,z15,z2,z4,z77,z314]),(0,[z7,z15,z2,z77,z13,z866]),(0,[z867,z15,z2,z3,z4,z42])],[(0,[z7,z48,z15,z345,z4,z13])],[(0,[z7,z48,z15,z2,z222,z13]),(0,[z337,z7,z2,z3,z4,z78])],[(0,[z302,z7,z15,z2,z32,z4])],[(0,[z7,z15,z2,z222,z868,z13]),(0,[z7,z15,z869,z2,z4,z13]),(0,[z7,z15,z2,z3,z870,z4]),(0,[z854,z7,z15,z2,z4,z5]),(0,[z15,z2,z3,z21,z95,z4])],[(0,[z7,z15,z2,z3,z4,z871]),(0,[z46,z90,z7,z2,z4,z13]),(0,[z7,z15,z2,z4,z872,z13])],[(0,[z477,z139,z7,z2,z4,z13]),(0,[z837,z7,z2,z3,z4,z13]),(0,[z16,z7,z15,z2,z4,z873])],[],[(0,[z7,z15,z2,z222,z77,z13]),(0,[z137,z15,z2,z3,z4,z874])],[(0,[z7,z15,z2,z3,z4,z205]),(0,[z315,z15,z2,z3,z32,z4])],[(0,[z7,z48,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z143,z5]),(0,[z875,z7,z15,z2,z4,z13]),(0,[z7,z15,z876,z2,z4,z13])],[(0,[z877,z7,z15,z2,z3,z4]),(0,[z7,z15,z27,z2,z4,z383]),(0,[z7,z15,z2,z3,z121,z5]),(0,[z7,z15,z2,z3,z735,z314]),(0,[z7,z15,z2,z3,z878,z9])],[(0,[z7,z15,z2,z3,z222,z13]),(0,[z416,z15,z149,z3,z4,z13]),(0,[z879,z15,z2,z3,z4,z5]),(0,[z16,z225,z7,z15,z2,z4]),(0,[z16,z7,z15,z2,z4,z646])],[(0,[z7,z15,z880,z2,z4,z13]),(0,[z7,z150,z2,z372,z4,z13]),(0,[z16,z7,z2,z268,z4,z5]),(0,[z46,z7,z2,z4,z22,z13]),(0,[z7,z15,z2,z4,z881,z13])],[(0,[z882,z16,z7,z2,z4,z13]),(0,[z7,z15,z2,z3,z883,z4])],[(0,[z7,z15,z149,z3,z4,z35]),(0,[z7,z15,z2,z4,z77,z446])],[(0,[z7,z11,z2,z3,z4,z33]),(0,[z7,z15,z2,z3,z884,z13]),(0,[z7,z15,z2,z3,z32,z885]),(0,[z7,z15,z2,z4,z13,z238]),(0,[z7,z15,z2,z3,z362,z168])],[(0,[z15,z2,z3,z4,z786,z5]),(0,[z7,z15,z2,z3,z4,z886])],[(0,[z7,z15,z2,z3,z4,z887]),(0,[z7,z15,z2,z3,z4,z888]),(0,[z15,z650,z2,z3,z21,z4])],[(0,[z7,z889,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z4,z890]),(0,[z7,z15,z27,z2,z4,z401]),(0,[z7,z15,z2,z4,z891,z13])],[(0,[z7,z15,z2,z4,z892,z13]),(0,[z7,z63,z97,z3,z4,z13])],[(0,[z54,z7,z2,z95,z4,z13]),(0,[z76,z304,z15,z2,z3,z4]),(0,[z15,z2,z3,z797,z168,z4])],[(0,[z7,z150,z2,z752,z4,z13]),(0,[z7,z15,z149,z3,z92,z13]),(0,[z16,z7,z86,z8,z4,z13]),(0,[z46,z405,z7,z2,z4,z13]),(0,[z893,z15,z2,z3,z4,z13])]],
   [[(0,[z7,z15,z2,z4,z77,z151]),(0,[z7,z15,z2,z3,z741,z9]),(0,[z16,z7,z15,z2,z4,z669])],[(0,[z16,z7,z293,z2,z4,z13]),(0,[z416,z63,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z32,z894])],[(0,[z7,z48,z15,z2,z4,z5]),(0,[z7,z15,z2,z3,z895,z4])],[(0,[z896,z7,z15,z2,z4,z13])],[(0,[z7,z15,z2,z3,z222,z5]),(0,[z7,z63,z2,z3,z4,z35]),(0,[z897,z15,z2,z3,z4,z13]),(0,[z7,z185,z2,z3,z4,z9])],[(0,[z898,z7,z15,z2,z3,z4])],[(0,[z7,z15,z2,z3,z4,z899]),(0,[z175,z7,z15,z3,z41,z446])],[(0,[z7,z15,z2,z900,z4,z901]),(0,[z902,z7,z15,z2,z3,z4]),(0,[z7,z15,z27,z2,z32,z9])],[(0,[z7,z2,z4,z787,z351,z13]),(0,[z7,z15,z2,z4,z903,z13]),(0,[z7,z48,z15,z2,z4,z198])],[(0,[z91,z15,z2,z3,z92,z262]),(0,[z7,z15,z345,z3,z4,z9]),(0,[z7,z15,z2,z123,z4,z119])],[(0,[z16,z76,z7,z2,z4,z78]),(0,[z7,z15,z2,z3,z32,z215]),(0,[z7,z15,z2,z3,z4,z904])],[(0,[z15,z1,z2,z3,z21,z4]),(0,[z7,z48,z15,z97,z4,z13]),(0,[z264,z15,z2,z8,z3,z4])],[],[(0,[z7,z15,z2,z905,z4,z13]),(0,[z906,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z907,z4,z13])],[(0,[z908,z7,z15,z2,z3,z13]),(0,[z7,z15,z2,z4,z13,z909]),(0,[z7,z48,z2,z4,z13,z910]),(0,[z7,z15,z911,z2,z4,z13])],[(0,[z16,z7,z63,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z912]),(0,[z7,z15,z2,z3,z4,z913])],[(0,[z46,z0,z7,z2,z4,z13]),(0,[z7,z15,z27,z2,z244,z4]),(0,[z7,z15,z2,z3,z526,z13]),(0,[z7,z914,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z4,z915]),(0,[z7,z15,z2,z567,z4,z79])],[(0,[z7,z15,z2,z453,z4,z9]),(0,[z7,z2,z3,z32,z4,z114])],[(0,[z7,z15,z2,z3,z4,z916]),(0,[z15,z2,z3,z4,z40,z5]),(0,[z313,z15,z2,z3,z4,z5]),(0,[z53,z7,z2,z123,z84,z13])],[(0,[z7,z15,z2,z917,z4,z13]),(0,[z7,z15,z2,z3,z918,z13]),(0,[z542,z7,z15,z27,z2,z4]),(0,[z7,z15,z2,z3,z4,z446])],[(0,[z7,z15,z2,z919,z4,z13])],[(0,[z7,z15,z2,z920,z4,z13]),(0,[z7,z150,z2,z3,z32,z4]),(0,[z7,z15,z921,z2,z4,z13]),(0,[z7,z15,z2,z343,z215,z13])],[(0,[z7,z15,z2,z3,z922,z4]),(0,[z7,z15,z2,z4,z351,z35]),(0,[z7,z15,z2,z923,z4,z13]),(0,[z924,z15,z2,z3,z4,z13])],[(0,[z882,z15,z2,z3,z4,z5]),(0,[z256,z15,z2,z141,z4,z35]),(0,[z16,z7,z135,z2,z4,z13]),(0,[z7,z15,z2,z925,z3,z4])],[(0,[z760,z7,z15,z3,z4,z71]),(0,[z7,z2,z3,z4,z114,z9])],[(0,[z15,z149,z3,z4,z13,z5]),(0,[z7,z15,z355,z3,z4,z35]),(0,[z926,z15,z2,z3,z4,z13]),(0,[z7,z44,z2,z3,z4,z446]),(0,[z7,z15,z2,z468,z215,z13]),(0,[z7,z15,z2,z180,z77,z13])],[(0,[z7,z15,z27,z2,z4,z439]),(0,[z46,z129,z7,z2,z4,z13]),(0,[z7,z15,z2,z927,z4,z13])],[(0,[z7,z928,z2,z3,z4,z13]),(0,[z83,z16,z7,z2,z4,z13]),(0,[z7,z15,z2,z929,z4,z13]),(0,[z59,z15,z2,z3,z4,z119])],[(0,[z94,z1,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z4,z930]),(0,[z931,z15,z2,z3,z4,z13]),(0,[z932,z15,z2,z3,z4,z13]),(0,[z630,z7,z44,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z933]),(0,[z7,z15,z2,z3,z214,z13])],[(0,[z7,z934,z15,z2,z4,z13]),(0,[z182,z7,z15,z3,z41,z13]),(0,[z7,z15,z2,z3,z4,z935]),(0,[z7,z15,z2,z506,z4,z13])],[(0,[z882,z7,z15,z2,z3,z9]),(0,[z7,z15,z2,z4,z77,z101])]],
   [[(0,[z7,z15,z2,z100,z4,z13]),(0,[z7,z135,z2,z3,z32,z4])],[],[(0,[z7,z15,z2,z4,z77,z389]),(0,[z137,z15,z27,z138,z4,z13]),(0,[z936,z15,z2,z3,z4,z13]),(0,[z225,z7,z15,z81,z2,z4]),(0,[z16,z7,z15,z210,z168,z13]),(0,[z7,z15,z937,z2,z215,z13])],[(0,[z46,z7,z138,z2,z4,z13]),(0,[z390,z7,z15,z2,z4,z9])],[],[(0,[z7,z15,z2,z938,z4,z13]),(0,[z53,z7,z15,z2,z3,z314]),(0,[z46,z7,z2,z295,z4,z13]),(0,[z46,z7,z2,z4,z41,z13]),(0,[z7,z15,z210,z3,z168,z9]),(0,[z7,z15,z2,z180,z77,z212]),(0,[z133,z15,z2,z3,z32,z9])],[(0,[z7,z15,z2,z3,z50,z314]),(0,[z67,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z95,z77,z9]),(0,[z7,z15,z2,z21,z4,z77])],[(0,[z7,z15,z2,z3,z4,z939]),(0,[z7,z15,z2,z3,z156,z50]),(1,[z15,z2,z3,z4,z520])],[(0,[z7,z15,z2,z180,z77,z5]),(0,[z7,z15,z2,z3,z940,z4]),(0,[z7,z48,z15,z2,z4,z941]),(0,[z15,z2,z3,z21,z4,z78]),(0,[z7,z159,z2,z3,z32,z4])],[(0,[z137,z15,z2,z3,z4,z151]),(0,[z7,z48,z15,z2,z4,z262]),(0,[z942,z67,z15,z2,z4,z13]),(0,[z7,z159,z2,z58,z4,z13])],[(0,[z7,z15,z27,z355,z4,z13])],[(0,[z7,z48,z15,z2,z4,z266]),(0,[z7,z15,z2,z3,z587,z4]),(0,[z76,z15,z2,z3,z21,z4])],[(0,[z7,z15,z27,z2,z4,z35]),(0,[z16,z932,z15,z2,z4,z13]),(0,[z15,z2,z3,z21,z4,z42])],[(0,[z15,z1,z2,z3,z156,z4]),(0,[z7,z15,z2,z121,z881,z13])],[(0,[z7,z15,z2,z943,z4,z13]),(0,[z7,z15,z2,z180,z77,z198])],[(0,[z91,z110,z2,z3,z4,z5]),(0,[z7,z15,z2,z100,z4,z5]),(0,[z15,z2,z3,z120,z797,z4])],[(0,[z0,z15,z27,z2,z4,z5]),(0,[z91,z15,z2,z557,z92,z13]),(0,[z15,z2,z3,z50,z4,z42]),(0,[z944,z15,z2,z3,z4,z13]),(0,[z7,z48,z15,z2,z384,z4]),(0,[z7,z15,z2,z3,z945,z9])],[(0,[z7,z15,z2,z3,z946,z4]),(0,[z7,z15,z2,z3,z4,z947]),(0,[z7,z15,z2,z3,z4,z948]),(0,[z7,z15,z2,z3,z28,z314]),(0,[z7,z15,z2,z949,z4,z13])],[(0,[z7,z48,z150,z2,z4,z13]),(0,[z15,z27,z2,z12,z4,z5]),(0,[z7,z15,z2,z3,z4,z941]),(0,[z186,z15,z2,z3,z4,z9])],[(0,[z7,z110,z2,z3,z4,z103]),(0,[z7,z15,z2,z3,z4,z950]),(0,[z37,z15,z2,z3,z4,z446]),(0,[z501,z15,z2,z3,z4,z9])],[(0,[z1,z2,z295,z3,z4,z5]),(0,[z54,z161,z7,z2,z4,z13]),(0,[z7,z15,z345,z3,z4,z119])],[(0,[z15,z625,z2,z3,z4,z5]),(0,[z7,z15,z951,z2,z4,z13])],[(0,[z7,z15,z2,z3,z215,z35]),(0,[z7,z15,z2,z3,z4,z952]),(0,[z953,z7,z15,z2,z4,z13]),(0,[z7,z308,z2,z3,z4,z9]),(0,[z7,z15,z2,z118,z4,z866])],[(0,[z7,z15,z2,z749,z4,z35])],[(0,[z10,z15,z12,z3,z4,z9]),(0,[z7,z15,z2,z4,z5,z238]),(0,[z7,z15,z2,z3,z32,z954])],[(0,[z7,z15,z955,z2,z4,z13]),(0,[z7,z15,z27,z2,z956,z13]),(0,[z7,z15,z2,z4,z77,z957])],[(0,[z7,z15,z958,z3,z4,z13]),(0,[z576,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z3,z4,z101]),(0,[z7,z15,z2,z3,z384,z4])],[(1,[z15,z2,z3,z21,z4]),(0,[z304,z15,z2,z468,z4,z13])],[(0,[z959,z15,z2,z3,z4,z35]),(0,[z54,z7,z15,z2,z4,z9]),(0,[z16,z7,z960,z2,z4,z13]),(0,[z53,z249,z2,z3,z84,z13])],[(0,[z7,z15,z2,z510,z4,z9]),(0,[z7,z15,z2,z3,z4,z961]),(0,[z7,z15,z2,z4,z77,z52]),(0,[z53,z7,z345,z3,z84,z13]),(0,[z7,z15,z2,z4,z77,z55])],[(0,[z7,z15,z2,z3,z4,z962]),(0,[z7,z2,z8,z330,z4,z13]),(0,[z7,z15,z2,z3,z4,z963]),(0,[z7,z48,z15,z2,z508,z9]),(0,[z7,z15,z2,z4,z13,z964]),(0,[z965,z966,z7,z15,z4,z13])],[(0,[z967,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z118,z4,z780])]],
   [[(0,[z15,z2,z517,z3,z4,z13]),(0,[z337,z7,z2,z3,z4,z968])],[(1,[z15,z2,z3,z74,z13]),(0,[z7,z15,z2,z453,z32,z4])],[(0,[z256,z15,z2,z3,z21,z4])],[(0,[z7,z1,z2,z510,z4,z13]),(0,[z7,z15,z27,z2,z77,z35]),(0,[z7,z15,z355,z123,z4,z13]),(1,[z7,z15,z2,z3,z336])],[(0,[z7,z15,z12,z3,z41,z9]),(0,[z7,z15,z2,z969,z4,z13]),(0,[z7,z15,z418,z2,z4,z35]),(0,[z7,z15,z2,z4,z13,z195]),(0,[z7,z15,z2,z4,z419,z35]),(0,[z7,z15,z81,z2,z598,z4])],[(0,[z337,z1,z2,z3,z4,z5]),(0,[z46,z137,z7,z2,z4,z13]),(0,[z16,z59,z15,z2,z4,z13]),(0,[z7,z15,z2,z970,z77,z13])],[],[(0,[z16,z416,z1,z2,z4,z13]),(0,[z7,z150,z2,z3,z222,z13]),(0,[z643,z15,z2,z3,z4,z5]),(0,[z7,z768,z2,z3,z4,z35]),(0,[z7,z15,z2,z4,z13,z971])],[(0,[z7,z48,z15,z2,z4,z341]),(0,[z0,z15,z2,z3,z4,z786]),(0,[z7,z15,z955,z2,z4,z5]),(0,[z7,z15,z2,z3,z508,z9])],[(0,[z7,z15,z2,z972,z4,z13]),(0,[z973,z7,z15,z2,z4,z335]),(0,[z7,z15,z2,z343,z32,z4]),(0,[z7,z15,z2,z3,z349,z9]),(0,[z15,z2,z3,z21,z735,z4])],[(0,[z7,z974,z15,z2,z4,z464]),(0,[z7,z15,z2,z3,z4,z975])],[(0,[z976,z7,z8,z3,z4,z13]),(0,[z7,z15,z2,z372,z4,z35]),(0,[z7,z15,z977,z2,z4,z13])],[(0,[z16,z7,z292,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z978]),(0,[z7,z110,z149,z3,z4,z13]),(0,[z91,z15,z2,z3,z28,z92]),(0,[z7,z15,z2,z4,z77,z42]),(0,[z979,z7,z8,z3,z4,z13])],[(0,[z7,z15,z2,z4,z5,z909]),(0,[z7,z15,z2,z3,z4,z980]),(0,[z7,z15,z2,z325,z3,z4]),(0,[z405,z7,z15,z58,z4,z13]),(0,[z981,z7,z308,z2,z4,z13]),(0,[z7,z15,z2,z468,z32,z4])],[(0,[z15,z2,z12,z3,z4,z151]),(1,[z15,z517,z3,z4,z13]),(0,[z7,z693,z308,z2,z4,z13])],[(0,[z7,z148,z15,z2,z32,z4]),(0,[z577,z7,z135,z2,z4,z13]),(0,[z7,z15,z2,z3,z168,z446]),(0,[z7,z15,z27,z2,z21,z4])],[(0,[z7,z15,z2,z4,z13,z545])],[(0,[z7,z412,z2,z4,z84,z13])],[(0,[z7,z15,z2,z3,z4,z341]),(0,[z46,z7,z2,z4,z982,z13])],[(0,[z7,z15,z2,z983,z4,z13]),(0,[z7,z15,z2,z4,z984,z13]),(0,[z7,z15,z2,z546,z77,z13]),(0,[z7,z15,z650,z3,z4,z480]),(0,[z7,z473,z2,z3,z32,z4])],[(0,[z7,z15,z2,z752,z4,z35]),(0,[z7,z15,z2,z985,z3,z4]),(0,[z16,z542,z7,z15,z2,z4]),(0,[z7,z15,z2,z3,z4,z957]),(0,[z986,z15,z2,z391,z4,z13])],[(0,[z59,z15,z355,z3,z4,z13])],[(0,[z7,z15,z2,z4,z792,z35]),(0,[z54,z7,z2,z69,z4,z13])],[(0,[z7,z15,z2,z3,z987,z13])],[(0,[z7,z15,z2,z3,z32,z222]),(0,[z16,z7,z86,z2,z4,z35]),(0,[z7,z15,z2,z3,z4,z55]),(0,[z46,z7,z2,z4,z77,z13])],[(0,[z7,z15,z2,z3,z988,z4]),(0,[z7,z15,z27,z2,z4,z183]),(0,[z53,z16,z7,z2,z4,z9]),(0,[z15,z2,z3,z21,z4,z4])],[(0,[z7,z15,z2,z557,z4,z13]),(0,[z7,z989,z2,z3,z4,z13]),(0,[z76,z113,z2,z3,z4,z78]),(0,[z46,z7,z2,z385,z4,z13])],[(0,[z7,z292,z15,z2,z4,z9]),(0,[z15,z2,z3,z50,z4,z5]),(0,[z7,z990,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z991,z4]),(0,[z15,z2,z3,z385,z21,z4])],[(0,[z7,z15,z992,z2,z4,z13]),(0,[z161,z7,z2,z510,z4,z13]),(0,[z405,z7,z15,z58,z4,z5])],[],[(0,[z7,z15,z2,z4,z993,z13]),(0,[z7,z15,z2,z3,z4,z994]),(0,[z286,z15,z2,z3,z32,z4])],[(0,[z16,z15,z1,z2,z4,z5]),(0,[z7,z11,z27,z2,z4,z13]),(0,[z7,z48,z2,z295,z4,z35]),(0,[z15,z2,z3,z21,z995,z4])]],
   [[(0,[z46,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z996,z13])],[(0,[z16,z7,z2,z997,z4,z13])],[(0,[z7,z48,z15,z2,z4,z383]),(0,[z256,z15,z625,z2,z4,z13]),(0,[z7,z15,z2,z3,z998,z4]),(0,[z186,z15,z2,z3,z32,z4])],[(0,[z7,z15,z97,z3,z32,z4]),(0,[z7,z15,z223,z2,z4,z9]),(0,[z7,z15,z999,z2,z4,z13])],[(0,[z7,z15,z2,z4,z868,z13]),(0,[z7,z15,z27,z2,z4,z33]),(0,[z15,z2,z3,z4,z1000,z5]),(0,[z7,z1001,z2,z3,z4,z13]),(0,[z274,z304,z15,z2,z3,z4]),(0,[z46,z7,z1002,z2,z4,z13])],[(0,[z7,z15,z2,z1003,z4,z13]),(0,[z7,z375,z2,z3,z4,z13]),(0,[z249,z15,z345,z3,z4,z13]),(0,[z53,z7,z2,z330,z84,z13])],[(0,[z252,z1,z2,z3,z32,z4]),(0,[z7,z15,z2,z23,z4,z35]),(0,[z6,z7,z263,z8,z4,z13]),(0,[z7,z308,z2,z3,z32,z4]),(0,[z70,z7,z15,z3,z215,z71])],[(0,[z46,z7,z2,z4,z77,z5]),(0,[z7,z48,z15,z2,z598,z4]),(0,[z53,z15,z2,z3,z21,z4]),(0,[z175,z15,z2,z3,z21,z4])],[(0,[z15,z2,z3,z4,z617,z5]),(0,[z7,z15,z2,z3,z1004,z4]),(0,[z16,z7,z15,z2,z32,z4]),(0,[z16,z7,z15,z2,z331,z9]),(0,[z7,z2,z295,z267,z4,z13]),(0,[z59,z15,z27,z2,z4,z13]),(0,[z1005,z15,z2,z3,z21,z4])],[(0,[z7,z15,z2,z557,z4,z5]),(0,[z7,z15,z2,z1006,z4,z13])],[(0,[z7,z48,z15,z2,z4,z401]),(0,[z225,z7,z15,z263,z2,z4]),(0,[z7,z960,z589,z3,z4,z13]),(0,[z16,z7,z15,z2,z305,z4]),(0,[z7,z15,z2,z4,z77,z24])],[(0,[z1007,z7,z15,z2,z4,z13]),(0,[z16,z7,z2,z384,z95,z4]),(0,[z7,z94,z2,z3,z563,z13]),(0,[z7,z15,z2,z3,z4,z1008])],[(0,[z7,z15,z2,z4,z1009,z13]),(0,[z7,z1010,z2,z3,z4,z13]),(0,[z7,z1011,z15,z2,z4,z13])],[(0,[z7,z15,z2,z510,z32,z4]),(0,[z7,z48,z2,z1012,z4,z13]),(0,[z542,z7,z15,z2,z3,z4]),(0,[z388,z7,z2,z3,z4,z13]),(0,[z133,z15,z2,z3,z21,z4])],[(0,[z7,z63,z149,z3,z4,z13]),(0,[z7,z44,z2,z4,z77,z13])],[(0,[z46,z7,z15,z2,z4,z5]),(0,[z7,z15,z2,z4,z13,z1013]),(0,[z7,z15,z2,z468,z121,z13]),(0,[z513,z15,z2,z3,z32,z4])],[(0,[z7,z1014,z15,z2,z4,z13]),(0,[z16,z7,z15,z2,z1015,z13]),(0,[z7,z15,z1016,z3,z4,z13]),(0,[z7,z15,z2,z4,z34,z9]),(0,[z7,z1017,z15,z2,z4,z13]),(0,[z966,z7,z15,z58,z4,z13]),(0,[z7,z135,z2,z3,z4,z446])],[(0,[z7,z15,z27,z2,z156,z4]),(0,[z203,z15,z27,z2,z4,z13])],[(0,[z7,z15,z999,z2,z4,z5]),(0,[z7,z15,z2,z3,z4,z1018])],[(0,[z1019,z15,z2,z3,z4,z5]),(0,[z91,z15,z97,z3,z92,z13]),(0,[z46,z7,z2,z3,z4,z13]),(0,[z7,z2,z4,z77,z740,z13])],[(0,[z7,z15,z2,z3,z4,z401]),(0,[z762,z15,z2,z155,z4,z13]),(0,[z6,z7,z8,z3,z32,z4]),(0,[z7,z15,z2,z4,z77,z212])],[(0,[z137,z15,z2,z3,z4,z42]),(0,[z53,z7,z2,z3,z331,z13]),(0,[z457,z48,z15,z2,z4,z13]),(0,[z7,z48,z15,z2,z32,z9]),(0,[z7,z15,z2,z3,z1020,z4]),(0,[z7,z2,z3,z4,z1021,z13])],[(0,[z7,z15,z2,z3,z4,z1022]),(0,[z7,z15,z2,z1023,z4,z13]),(0,[z7,z1024,z2,z3,z4,z13])],[(0,[z1025,z15,z2,z3,z50,z13]),(0,[z15,z1026,z2,z3,z4,z5]),(0,[z15,z2,z1027,z3,z4,z5])],[(0,[z7,z1028,z15,z2,z4,z13]),(0,[z175,z7,z15,z3,z41,z24])],[(0,[z139,z7,z2,z155,z4,z13]),(0,[z7,z15,z2,z3,z4,z1029]),(0,[z7,z1030,z2,z3,z4,z13]),(0,[z7,z15,z2,z168,z77,z9])],[(0,[z16,z0,z15,z2,z4,z5]),(0,[z91,z15,z2,z3,z92,z35]),(0,[z7,z15,z2,z4,z1031,z13]),(0,[z7,z1032,z2,z3,z4,z13]),(0,[z7,z15,z420,z2,z4,z35]),(0,[z352,z15,z2,z3,z32,z4])],[(0,[z15,z2,z3,z21,z50,z4]),(0,[z90,z15,z2,z3,z4,z520]),(0,[z15,z2,z1033,z3,z4,z5]),(0,[z59,z94,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1034])],[(0,[z129,z15,z2,z155,z4,z439]),(0,[z7,z15,z27,z2,z132,z13])],[(0,[z16,z7,z2,z524,z4,z13]),(0,[z7,z11,z2,z372,z4,z13]),(0,[z7,z48,z15,z2,z244,z4]),(0,[z16,z7,z1035,z2,z4,z13])],[(0,[z7,z86,z2,z4,z331,z13]),(0,[z7,z94,z2,z3,z95,z9])]],
   [[(0,[z7,z15,z2,z3,z1036,z4]),(0,[z7,z110,z27,z2,z4,z13]),(0,[z16,z7,z15,z2,z120,z4]),(0,[z113,z15,z2,z4,z77,z13]),(0,[z7,z15,z2,z215,z370,z13]),(0,[z7,z1037,z2,z3,z4,z9])],[(0,[z7,z110,z2,z300,z4,z13]),(0,[z7,z15,z2,z3,z4,z1038]),(0,[z7,z15,z2,z4,z331,z13])],[(0,[z7,z15,z2,z3,z4,z1039]),(0,[z1040,z7,z2,z3,z4,z13]),(0,[z15,z2,z3,z21,z4,z79])],[(0,[z7,z15,z2,z372,z4,z33]),(0,[z15,z2,z149,z3,z4,z5]),(0,[z31,z15,z2,z3,z4,z13])],[(0,[z49,z15,z2,z3,z244,z50]),(0,[z53,z16,z7,z2,z4,z119]),(0,[z7,z15,z2,z3,z4,z1041]),(0,[z7,z412,z15,z2,z4,z9])],[(0,[z137,z15,z2,z4,z77,z5]),(0,[z7,z15,z2,z3,z4,z1042]),(0,[z1043,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1044]),(0,[z7,z15,z2,z440,z4,z5]),(0,[z7,z86,z57,z3,z4,z13]),(0,[z7,z15,z2,z32,z4,z88])],[(0,[z7,z11,z2,z752,z4,z13]),(1,[z46,z7,z2,z4,z13]),(0,[z7,z15,z2,z3,z1045,z4])],[(0,[z7,z48,z15,z2,z4,z439]),(0,[z37,z15,z2,z4,z77,z13]),(0,[z7,z1046,z135,z2,z4,z13])],[(0,[z7,z1032,z2,z3,z4,z5])],[(0,[z7,z15,z2,z4,z1047,z13]),(1,[z37,z15,z3,z41,z13]),(0,[z7,z15,z122,z2,z4,z9])],[(0,[z7,z15,z2,z1048,z4,z13]),(0,[z7,z15,z2,z3,z703,z4]),(0,[z7,z2,z295,z4,z88,z13]),(0,[z7,z44,z2,z3,z4,z24]),(0,[z7,z15,z210,z3,z32,z168]),(0,[z7,z15,z269,z2,z4,z1049])],[(0,[z7,z15,z2,z66,z4,z13]),(0,[z7,z15,z2,z752,z4,z33])],[(0,[z7,z15,z1050,z2,z4,z13]),(0,[z7,z15,z3,z4,z13,z480]),(0,[z7,z15,z2,z3,z4,z1051]),(0,[z7,z15,z2,z131,z4,z9])],[(0,[z7,z15,z2,z1052,z3,z13]),(0,[z16,z7,z2,z268,z4,z35]),(0,[z405,z7,z159,z58,z4,z13]),(0,[z203,z15,z2,z3,z4,z777])],[(0,[z7,z108,z11,z2,z4,z13]),(0,[z139,z7,z2,z3,z4,z9])],[(0,[z137,z48,z15,z138,z4,z13]),(0,[z7,z15,z2,z557,z4,z262]),(0,[z7,z15,z2,z4,z331,z5]),(0,[z1053,z15,z2,z3,z4,z5]),(0,[z7,z15,z937,z2,z4,z13])],[(0,[z16,z7,z2,z1054,z4,z13]),(0,[z7,z15,z2,z3,z4,z1055]),(0,[z7,z15,z2,z453,z4,z446]),(0,[z274,z15,z2,z3,z21,z4])],[(0,[z137,z15,z138,z3,z4,z401]),(0,[z7,z15,z2,z3,z4,z439]),(0,[z7,z15,z2,z234,z3,z336])],[(0,[z7,z15,z2,z4,z187,z659])],[(0,[z7,z15,z1056,z2,z4,z13]),(0,[z292,z15,z1,z2,z4,z5]),(0,[z1057,z7,z15,z2,z4,z13]),(0,[z7,z94,z15,z2,z34,z13]),(0,[z7,z94,z345,z3,z4,z13]),(0,[z53,z7,z2,z3,z84,z9]),(0,[z7,z15,z2,z1058,z4,z187])],[(0,[z7,z15,z2,z1059,z4,z187]),(0,[z7,z15,z317,z193,z4,z13]),(0,[z15,z2,z3,z21,z168,z4])],[(0,[z16,z1,z2,z4,z13,z5]),(0,[z416,z15,z2,z3,z4,z205]),(0,[z7,z15,z2,z3,z1060,z4]),(1,[z46,z7,z2,z4,z5]),(0,[z7,z15,z2,z468,z4,z5]),(1,[z7,z15,z317,z4,z13]),(0,[z7,z2,z3,z4,z13,z629])],[(0,[z16,z7,z15,z2,z4,z205])],[(0,[z1061,z7,z15,z2,z3,z4]),(0,[z7,z48,z15,z355,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1062]),(0,[z7,z15,z2,z1063,z4,z13]),(0,[z15,z2,z21,z4,z77,z13]),(0,[z7,z15,z2,z4,z349,z187])],[(0,[z216,z252,z1,z2,z4,z13]),(0,[z15,z2,z12,z3,z4,z42]),(0,[z7,z15,z2,z3,z4,z1064]),(0,[z7,z48,z15,z2,z4,z35]),(0,[z7,z1065,z2,z3,z4,z13])],[(0,[z113,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z510,z4,z205]),(0,[z7,z15,z2,z3,z222,z35]),(0,[z7,z2,z3,z4,z642,z13]),(0,[z15,z2,z3,z4,z5,z191]),(0,[z7,z15,z2,z568,z3,z28]),(0,[z7,z15,z2,z598,z3,z4]),(0,[z7,z15,z2,z297,z4,z13]),(0,[z37,z15,z3,z4,z41,z13])],[(0,[z7,z11,z2,z3,z32,z4]),(0,[z7,z15,z2,z3,z1066,z4]),(1,[z63,z2,z3,z4,z5]),(0,[z1067,z15,z2,z3,z4,z13])],[(0,[z0,z48,z15,z2,z4,z5])],[(0,[z15,z2,z3,z4,z205,z5]),(0,[z10,z15,z2,z3,z21,z4]),(0,[z137,z15,z1068,z3,z4,z13]),(0,[z728,z16,z7,z2,z4,z13]),(0,[z7,z15,z2,z121,z77,z13])]],
   [[(0,[z137,z15,z2,z3,z4,z5]),(0,[z670,z7,z27,z2,z4,z13])],[(0,[z710,z7,z63,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1069]),(0,[z7,z15,z1070,z2,z4,z13]),(0,[z1071,z15,z2,z3,z21,z4])],[(0,[z7,z63,z27,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1072]),(0,[z1073,z7,z15,z2,z275,z4])],[(0,[z7,z15,z2,z3,z4,z1074]),(0,[z7,z2,z3,z4,z563,z13]),(0,[z7,z15,z210,z3,z120,z168]),(0,[z7,z15,z27,z2,z371,z13])],[(0,[z7,z15,z149,z3,z4,z9]),(0,[z7,z15,z2,z1075,z3,z4])],[(0,[z7,z15,z2,z4,z1076,z13]),(0,[z7,z15,z2,z1077,z4,z13]),(0,[z37,z15,z2,z3,z4,z24])],[(1,[z15,z2,z130,z4,z13]),(0,[z7,z226,z308,z2,z3,z4]),(0,[z46,z1078,z7,z2,z4,z13]),(0,[z133,z15,z2,z32,z4,z77])],[(0,[z1079,z7,z15,z58,z4,z13]),(0,[z1080,z15,z625,z2,z4,z13]),(0,[z76,z7,z48,z2,z4,z78]),(0,[z7,z48,z2,z267,z4,z13]),(0,[z1081,z15,z2,z3,z4,z13])],[(0,[z7,z15,z1082,z3,z4,z13]),(0,[z7,z48,z11,z2,z4,z13]),(0,[z7,z15,z2,z4,z1083,z13]),(0,[z819,z7,z2,z168,z4,z13]),(0,[z304,z185,z2,z3,z4,z13])],[(0,[z16,z137,z15,z138,z4,z13]),(0,[z16,z7,z15,z2,z4,z314]),(0,[z1084,z15,z2,z3,z4,z35]),(0,[z37,z44,z2,z3,z4,z13]),(0,[z7,z15,z650,z3,z4,z484]),(0,[z7,z15,z2,z208,z4,z9])],[(0,[z15,z2,z12,z4,z77,z5]),(0,[z7,z15,z1085,z3,z4,z13]),(0,[z113,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z1086,z4,z13]),(0,[z542,z7,z15,z2,z4,z79])],[(0,[z16,z15,z2,z21,z4,z13]),(0,[z46,z7,z48,z2,z4,z13]),(0,[z203,z15,z2,z23,z4,z13]),(0,[z7,z15,z2,z4,z77,z356])],[(0,[z7,z15,z2,z1087,z4,z13]),(0,[z7,z15,z2,z3,z1088,z4])],[(0,[z216,z7,z15,z2,z4,z9]),(0,[z256,z15,z2,z130,z4,z13]),(0,[z15,z2,z568,z3,z4,z5])],[(0,[z1089,z48,z15,z2,z4,z5]),(0,[z7,z15,z209,z3,z4,z13]),(0,[z133,z15,z27,z2,z32,z4])],[(0,[z7,z1014,z150,z2,z4,z13]),(0,[z203,z15,z2,z3,z32,z4]),(0,[z7,z15,z2,z1090,z4,z13])],[(0,[z1091,z15,z2,z3,z4,z13]),(0,[z1092,z7,z15,z2,z4,z13])],[(0,[z7,z1093,z15,z2,z4,z13]),(0,[z46,z7,z178,z2,z4,z13])],[],[(0,[z7,z15,z2,z3,z509,z9]),(0,[z16,z7,z48,z2,z32,z4]),(0,[z53,z46,z7,z2,z4,z13]),(0,[z7,z412,z2,z295,z4,z13]),(0,[z175,z46,z7,z2,z4,z13])],[(0,[z7,z15,z2,z1094,z4,z13]),(0,[z7,z412,z15,z2,z32,z4])],[(0,[z1095,z16,z7,z2,z4,z13]),(0,[z7,z15,z2,z118,z4,z901]),(0,[z7,z86,z1096,z3,z4,z13])],[(0,[z882,z15,z2,z3,z92,z13]),(0,[z46,z7,z1,z2,z4,z13]),(0,[z7,z1097,z15,z2,z4,z13]),(0,[z175,z37,z15,z3,z41,z13]),(0,[z7,z1098,z15,z2,z4,z13]),(0,[z7,z15,z2,z118,z3,z215])],[(0,[z7,z15,z2,z4,z1083,z5]),(0,[z7,z15,z2,z168,z284,z9])],[(0,[z7,z15,z2,z3,z4,z1099]),(0,[z1089,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z770,z13]),(0,[z16,z7,z15,z2,z4,z446])],[(0,[z7,z15,z2,z3,z1100,z9]),(0,[z7,z15,z1101,z3,z4,z13]),(0,[z7,z15,z2,z4,z1102,z13])],[(0,[z16,z7,z15,z97,z4,z13]),(0,[z7,z2,z4,z114,z88,z13]),(0,[z7,z241,z2,z3,z4,z9])],[],[(0,[z7,z15,z2,z3,z4,z1103]),(0,[z15,z2,z3,z21,z4,z92]),(0,[z1104,z15,z2,z3,z4,z13]),(0,[z7,z1105,z15,z2,z4,z13]),(0,[z249,z15,z2,z3,z4,z9]),(0,[z7,z15,z2,z1045,z4,z77])],[(0,[z7,z48,z15,z2,z21,z4])],[(0,[z7,z11,z2,z3,z143,z13]),(0,[z7,z15,z138,z3,z41,z9]),(0,[z16,z15,z2,z50,z4,z5]),(0,[z7,z15,z2,z118,z468,z4])],[(0,[z282,z15,z2,z3,z92,z13]),(0,[z7,z15,z2,z255,z4,z9]),(0,[z7,z2,z3,z4,z13,z116]),(0,[z7,z1106,z27,z2,z4,z13])]],
   [[(0,[z16,z7,z15,z2,z4,z151]),(0,[z7,z15,z2,z3,z1107,z4]),(0,[z7,z15,z2,z180,z77,z35])],[(0,[z619,z7,z15,z2,z4,z13]),(0,[z1108,z7,z15,z2,z3,z4]),(0,[z7,z15,z2,z1109,z4,z13])],[(0,[z7,z15,z2,z1110,z4,z13]),(1,[z264,z15,z2,z3,z4]),(0,[z1111,z16,z7,z15,z2,z4]),(0,[z7,z15,z27,z210,z168,z13])],[(0,[z256,z15,z2,z141,z4,z9]),(0,[z7,z15,z1112,z2,z4,z13])],[(0,[z7,z1113,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z1114,z4])],[(0,[z1115,z15,z2,z3,z4,z13]),(0,[z7,z135,z2,z4,z77,z13])],[(0,[z7,z15,z122,z2,z168,z9])],[(0,[z1116,z7,z48,z2,z4,z13]),(0,[z7,z15,z2,z3,z21,z4]),(0,[z7,z48,z15,z2,z4,z183]),(0,[z7,z15,z2,z100,z4,z35]),(0,[z16,z7,z2,z95,z4,z9]),(0,[z7,z15,z27,z2,z96,z13])],[(0,[z256,z293,z2,z141,z4,z13]),(0,[z76,z7,z2,z4,z166,z78])],[(0,[z7,z15,z2,z4,z1117,z13]),(0,[z7,z15,z2,z4,z13,z1118]),(0,[z7,z15,z2,z3,z4,z1119]),(0,[z53,z7,z2,z4,z331,z13]),(0,[z7,z15,z27,z2,z1120,z13]),(0,[z7,z15,z2,z120,z4,z77])],[(0,[z16,z7,z15,z1121,z4,z13]),(0,[z1122,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z4,z1123,z13]),(0,[z59,z15,z2,z3,z4,z865]),(0,[z7,z15,z2,z3,z336,z4])],[(0,[z237,z252,z2,z3,z4,z13]),(0,[z16,z7,z1124,z2,z4,z13]),(0,[z7,z2,z8,z255,z4,z13]),(0,[z7,z15,z27,z2,z4,z695])],[(0,[z7,z15,z2,z1125,z4,z13]),(0,[z7,z159,z2,z4,z77,z13])],[(0,[z1126,z7,z15,z2,z4,z13]),(0,[z91,z110,z2,z3,z92,z13]),(0,[z743,z7,z15,z3,z41,z13]),(0,[z542,z7,z15,z2,z118,z4])],[(0,[z7,z11,z2,z3,z222,z13]),(0,[z7,z48,z44,z2,z4,z13])],[(0,[z15,z2,z3,z4,z35,z5]),(0,[z416,z15,z27,z2,z4,z35])],[(0,[z7,z15,z2,z1127,z3,z4]),(0,[z91,z15,z2,z3,z1100,z13])],[(0,[z7,z48,z15,z2,z4,z33]),(0,[z760,z7,z15,z3,z41,z13])],[(0,[z7,z15,z2,z3,z4,z535])],[(0,[z7,z15,z2,z3,z222,z33]),(0,[z7,z15,z149,z3,z32,z4])],[(0,[z368,z15,z2,z3,z4,z13]),(0,[z16,z7,z2,z177,z4,z13])],[(0,[z7,z15,z2,z3,z1128,z4]),(0,[z16,z49,z1,z2,z4,z13]),(0,[z7,z1129,z2,z3,z4,z13]),(0,[z59,z48,z15,z2,z4,z13]),(0,[z7,z15,z2,z1130,z4,z13])],[(0,[z16,z15,z2,z3,z21,z4]),(0,[z7,z48,z308,z2,z4,z13])],[(0,[z10,z15,z12,z752,z4,z13]),(0,[z7,z1131,z2,z3,z4,z13]),(0,[z16,z7,z2,z100,z4,z13]),(0,[z7,z15,z27,z2,z4,z9])],[(0,[z48,z15,z1,z2,z4,z5]),(0,[z7,z15,z2,z300,z4,z9]),(0,[z7,z15,z2,z4,z77,z189])],[(0,[z405,z7,z15,z677,z4,z13]),(0,[z7,z15,z2,z3,z1132,z9])],[(0,[z16,z7,z2,z290,z4,z13]),(0,[z7,z15,z2,z3,z4,z1133])],[(0,[z781,z15,z12,z3,z4,z13]),(0,[z7,z185,z2,z3,z121,z13])],[(0,[z7,z293,z27,z2,z4,z13]),(0,[z7,z15,z2,z123,z4,z5]),(0,[z15,z2,z3,z193,z21,z4])],[(0,[z15,z2,z141,z3,z21,z4]),(0,[z16,z7,z1134,z2,z4,z13]),(0,[z7,z15,z2,z1135,z4,z13])],[(0,[z7,z48,z15,z2,z156,z4]),(0,[z7,z81,z2,z295,z4,z13]),(0,[z16,z7,z15,z2,z4,z101]),(0,[z16,z7,z15,z650,z4,z160]),(0,[z203,z48,z15,z2,z4,z13]),(0,[z7,z44,z210,z3,z4,z13])]],
   [[(0,[z59,z15,z2,z3,z4,z13]),(0,[z7,z63,z2,z3,z32,z4]),(0,[z7,z48,z15,z2,z4,z1136]),(0,[z7,z15,z650,z3,z1137,z4])],[(0,[z15,z2,z3,z4,z874,z5]),(0,[z15,z2,z50,z4,z351,z5]),(0,[z7,z15,z2,z4,z1138,z13]),(0,[z16,z7,z2,z4,z1139,z9])],[(0,[z7,z135,z2,z3,z4,z24]),(0,[z7,z15,z2,z3,z215,z9])],[(0,[z1140,z15,z2,z3,z4,z5]),(0,[z16,z7,z2,z1141,z4,z13]),(0,[z7,z15,z3,z4,z160,z480])],[(0,[z7,z15,z2,z4,z77,z218])],[],[(0,[z7,z15,z2,z3,z4,z1142]),(0,[z16,z7,z2,z970,z4,z13]),(0,[z576,z15,z2,z3,z4,z9]),(0,[z7,z15,z2,z3,z4,z1143])],[(0,[z7,z15,z1144,z3,z4,z13]),(0,[z46,z7,z2,z8,z4,z13]),(0,[z249,z15,z2,z3,z4,z119]),(0,[z7,z15,z2,z1145,z4,z13]),(0,[z46,z7,z2,z4,z13,z9])],[(0,[z7,z15,z2,z1146,z4,z13]),(0,[z16,z7,z1147,z2,z4,z13]),(0,[z1148,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1149])],[(0,[z7,z15,z2,z3,z4,z1136]),(0,[z7,z15,z2,z3,z4,z1150])],[(0,[z252,z292,z1,z2,z4,z13]),(0,[z781,z15,z12,z3,z4,z5]),(0,[z49,z15,z27,z2,z50,z13]),(0,[z15,z2,z3,z4,z1151,z13])],[(0,[z7,z1152,z2,z3,z4,z13]),(1,[z7,z2,z3,z563,z13]),(0,[z7,z2,z3,z4,z116,z78])],[],[(0,[z16,z7,z2,z1153,z4,z13]),(0,[z53,z7,z2,z3,z32,z84])],[(0,[z7,z15,z2,z1154,z77,z13]),(0,[z46,z7,z2,z4,z92,z13]),(0,[z19,z7,z2,z4,z351,z13]),(0,[z59,z15,z2,z3,z4,z5]),(0,[z46,z7,z210,z2,z4,z13])],[(0,[z7,z1155,z2,z3,z4,z13]),(0,[z7,z15,z1156,z2,z4,z13]),(0,[z91,z63,z2,z3,z92,z13]),(0,[z627,z48,z15,z2,z4,z13]),(0,[z7,z327,z2,z3,z4,z13])],[(0,[z7,z1157,z15,z2,z4,z13]),(0,[z15,z27,z2,z32,z21,z4])],[(0,[z7,z15,z2,z1158,z4,z13]),(0,[z7,z15,z2,z699,z32,z4])],[(0,[z256,z15,z2,z141,z32,z4])],[(0,[z7,z15,z2,z4,z1159,z13]),(0,[z405,z7,z15,z58,z4,z35]),(0,[z7,z185,z2,z3,z4,z13]),(0,[z1160,z7,z15,z2,z4,z13]),(0,[z175,z7,z15,z453,z41,z13])],[(0,[z7,z15,z355,z3,z32,z4])],[(0,[z16,z7,z2,z1161,z4,z13]),(0,[z7,z15,z2,z4,z1162,z13]),(0,[z133,z15,z2,z3,z4,z9])],[(0,[z7,z1163,z48,z2,z4,z13]),(0,[z705,z15,z2,z3,z32,z4])],[(0,[z7,z110,z2,z3,z4,z13]),(0,[z16,z7,z1,z2,z4,z13]),(0,[z7,z1164,z15,z2,z4,z13]),(0,[z7,z15,z2,z379,z4,z9]),(1,[z15,z2,z3,z797,z4]),(0,[z7,z2,z668,z4,z77,z13])],[(0,[z139,z7,z2,z3,z4,z273]),(0,[z91,z16,z15,z2,z4,z5]),(0,[z7,z15,z345,z3,z4,z13]),(0,[z7,z15,z2,z4,z13,z1165]),(0,[z7,z15,z1166,z3,z4,z13]),(0,[z37,z15,z210,z3,z4,z13])],[(0,[z7,z15,z2,z3,z580,z143]),(0,[z7,z15,z97,z557,z4,z13]),(0,[z1167,z15,z2,z3,z4,z5]),(0,[z7,z1168,z2,z3,z4,z13]),(0,[z7,z15,z122,z2,z4,z246])],[],[],[(0,[z16,z161,z7,z2,z4,z9]),(0,[z49,z7,z15,z2,z77,z9]),(0,[z16,z7,z15,z2,z4,z52]),(0,[z1169,z15,z2,z3,z4,z5]),(0,[z16,z7,z15,z2,z4,z55])],[],[(0,[z7,z15,z2,z4,z13,z518]),(0,[z46,z7,z2,z4,z77,z35])]],
   [[(0,[z7,z15,z2,z752,z4,z9]),(0,[z91,z15,z2,z300,z4,z5]),(0,[z15,z2,z3,z4,z5,z1170]),(0,[z16,z7,z1171,z2,z4,z13]),(0,[z37,z135,z2,z3,z4,z13]),(0,[z687,z15,z2,z3,z120,z4]),(0,[z7,z15,z2,z32,z4,z77])],[(0,[z15,z2,z3,z4,z1172,z5]),(0,[z7,z15,z2,z3,z4,z1173]),(0,[z7,z15,z2,z557,z4,z35]),(0,[z49,z15,z2,z50,z351,z13]),(0,[z7,z15,z2,z4,z9,z238])],[(0,[z7,z15,z2,z3,z4,z1174])],[(0,[z7,z185,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z1175,z13]),(0,[z59,z15,z2,z100,z4,z13]),(0,[z7,z15,z2,z453,z4,z24])],[(0,[z7,z15,z2,z300,z4,z103]),(0,[z7,z15,z2,z1059,z4,z1176]),(0,[z304,z15,z2,z3,z4,z9]),(0,[z7,z15,z27,z2,z842,z13])],[(0,[z83,z7,z15,z3,z41,z13]),(0,[z76,z576,z2,z3,z4,z78]),(0,[z374,z7,z2,z3,z4,z78]),(0,[z7,z15,z2,z3,z4,z1177])],[(0,[z1111,z7,z15,z2,z3,z4]),(0,[z1178,z15,z2,z3,z4,z13])],[(0,[z16,z7,z1,z2,z4,z5]),(0,[z7,z110,z2,z3,z4,z5]),(0,[z46,z7,z15,z2,z4,z35]),(0,[z7,z15,z2,z3,z4,z873]),(0,[z1122,z15,z2,z3,z384,z4]),(0,[z7,z44,z2,z453,z4,z13]),(0,[z186,z15,z2,z4,z77,z13])],[(0,[z7,z15,z345,z3,z4,z5]),(0,[z7,z15,z2,z4,z5,z1118]),(0,[z7,z2,z3,z4,z114,z13]),(0,[z7,z15,z1179,z2,z4,z13]),(1,[z7,z15,z3,z4,z480]),(0,[z7,z15,z27,z2,z32,z4]),(0,[z162,z15,z2,z4,z47,z13])],[(0,[z7,z15,z263,z2,z4,z13]),(0,[z16,z7,z2,z677,z4,z13]),(0,[z15,z2,z3,z587,z95,z4]),(0,[z7,z15,z2,z3,z4,z235])],[(0,[z7,z15,z1180,z2,z4,z13]),(0,[z7,z15,z2,z1181,z3,z4]),(0,[z7,z15,z2,z1182,z3,z4]),(0,[z7,z1183,z27,z2,z4,z13])],[(0,[z252,z1,z2,z4,z77,z13]),(0,[z1184,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z234,z331,z13]),(0,[z7,z15,z2,z123,z4,z101]),(0,[z7,z308,z2,z4,z77,z13]),(0,[z7,z15,z2,z3,z4,z1185]),(0,[z7,z15,z2,z4,z13,z833])],[(0,[z16,z139,z7,z2,z4,z13]),(0,[z7,z15,z27,z149,z4,z13]),(0,[z16,z7,z59,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1186])],[(0,[z175,z203,z15,z3,z41,z13])],[],[(0,[z10,z15,z12,z3,z143,z13]),(0,[z7,z48,z293,z2,z4,z13]),(0,[z15,z2,z3,z4,z520,z5]),(0,[z16,z7,z15,z36,z4,z13]),(0,[z7,z15,z2,z1187,z4,z13]),(0,[z15,z2,z1188,z3,z21,z4])],[(0,[z7,z15,z2,z3,z4,z1189]),(0,[z16,z7,z1190,z2,z4,z13]),(0,[z7,z15,z2,z120,z4,z284]),(0,[z7,z15,z2,z118,z1191,z4]),(0,[z274,z7,z15,z2,z4,z1192])],[(0,[z7,z15,z1193,z2,z3,z9]),(0,[z7,z15,z2,z3,z4,z1194]),(0,[z7,z48,z15,z2,z4,z674]),(0,[z7,z15,z27,z2,z32,z96])],[(0,[z16,z7,z2,z859,z4,z13]),(0,[z16,z7,z15,z45,z4,z13]),(0,[z7,z15,z2,z23,z4,z9])],[(0,[z225,z7,z48,z15,z2,z4]),(0,[z1195,z7,z15,z2,z4,z831]),(0,[z16,z113,z15,z2,z4,z13]),(0,[z390,z7,z15,z2,z4,z13]),(0,[z7,z1046,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z638,z9])],[(1,[z16,z7,z345,z4,z13]),(0,[z7,z15,z27,z2,z168,z9]),(0,[z513,z15,z2,z4,z77,z13])],[(1,[z16,z1,z2,z4,z5]),(0,[z46,z7,z2,z50,z4,z13]),(0,[z46,z7,z2,z4,z13,z285])],[(0,[z7,z15,z2,z77,z35,z314]),(0,[z16,z7,z15,z2,z598,z4]),(0,[z576,z15,z2,z3,z32,z4]),(0,[z7,z1196,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1197]),(0,[z7,z2,z3,z4,z114,z5]),(0,[z7,z15,z1198,z2,z4,z13]),(0,[z7,z15,z1199,z552,z4,z13]),(0,[z1073,z15,z2,z3,z21,z4])],[(0,[z7,z15,z263,z2,z4,z5]),(0,[z7,z15,z2,z3,z4,z1200]),(0,[z53,z7,z2,z3,z563,z13])],[(0,[z90,z15,z27,z2,z4,z5]),(0,[z7,z15,z2,z276,z77,z13])],[(0,[z7,z15,z2,z4,z77,z340]),(0,[z7,z15,z2,z4,z1201,z13]),(0,[z46,z7,z2,z3,z4,z35]),(1,[z16,z59,z2,z4,z13])],[(0,[z1202,z15,z2,z4,z77,z13]),(0,[z15,z2,z3,z1203,z21,z4])],[(0,[z7,z15,z2,z3,z4,z1204]),(0,[z15,z2,z3,z50,z74,z13]),(0,[z133,z48,z15,z2,z32,z4]),(0,[z7,z15,z2,z4,z88,z55]),(0,[z274,z7,z15,z2,z4,z79])],[(0,[z7,z48,z63,z2,z4,z13]),(0,[z7,z15,z149,z300,z4,z13])],[(0,[z7,z15,z2,z3,z663,z9]),(0,[z286,z15,z2,z3,z4,z13])],[(0,[z7,z15,z2,z3,z1205,z13]),(0,[z16,z7,z2,z1206,z4,z13]),(0,[z7,z86,z2,z330,z4,z13])]],
   [[(0,[z10,z15,z12,z3,z222,z13]),(0,[z15,z2,z3,z50,z4,z183]),(0,[z7,z15,z418,z2,z32,z4]),(0,[z15,z2,z3,z384,z587,z4])],[(0,[z7,z1207,z2,z3,z4,z13]),(0,[z7,z15,z2,z330,z4,z13]),(0,[z37,z15,z2,z453,z4,z13])],[(0,[z15,z2,z149,z3,z92,z13]),(0,[z390,z7,z15,z2,z4,z5])],[(0,[z91,z15,z2,z92,z77,z13]),(0,[z16,z46,z7,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1208])],[(0,[z91,z7,z15,z2,z77,z9])],[(0,[z7,z48,z15,z2,z702,z4]),(0,[z48,z15,z2,z21,z4,z13])],[(0,[z91,z15,z2,z3,z92,z9]),(0,[z1209,z7,z15,z2,z4,z13]),(0,[z7,z2,z95,z4,z331,z13]),(0,[z7,z15,z3,z4,z480,z71]),(0,[z7,z15,z2,z118,z4,z1049])],[(0,[z1210,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z372,z32,z4]),(0,[z576,z15,z650,z2,z3,z4])],[(0,[z10,z15,z12,z3,z4,z13]),(0,[z7,z15,z2,z4,z331,z35]),(0,[z15,z192,z2,z3,z21,z4]),(0,[z133,z15,z2,z234,z3,z32])],[(0,[z7,z63,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z4,z60]),(0,[z7,z15,z1211,z2,z4,z13]),(0,[z7,z15,z27,z2,z127,z13]),(0,[z7,z15,z650,z3,z4,z160])],[(0,[z1212,z7,z15,z2,z331,z13]),(0,[z16,z7,z15,z2,z4,z24])],[(0,[z7,z48,z15,z2,z4,z340]),(0,[z15,z2,z3,z155,z21,z4]),(0,[z225,z7,z15,z2,z4,z77]),(0,[z7,z15,z2,z3,z4,z1213])],[(0,[z46,z7,z86,z2,z4,z13]),(0,[z54,z7,z15,z2,z4,z13]),(0,[z70,z576,z15,z2,z3,z4]),(0,[z175,z7,z15,z27,z41,z13])],[(0,[z7,z15,z2,z3,z4,z1214]),(0,[z7,z15,z2,z3,z1215,z4]),(0,[z256,z15,z2,z141,z4,z273]),(0,[z7,z15,z757,z193,z4,z13]),(0,[z7,z15,z2,z4,z13,z309])],[(0,[z7,z15,z210,z3,z862,z13]),(0,[z7,z110,z2,z3,z4,z262]),(1,[z46,z7,z2,z4,z35]),(0,[z7,z2,z4,z114,z77,z9])],[(0,[z15,z2,z3,z21,z4,z71])],[(0,[z7,z15,z2,z752,z32,z4]),(1,[z15,z149,z3,z92,z13]),(0,[z7,z15,z2,z330,z4,z5]),(0,[z1216,z15,z2,z3,z4,z35]),(0,[z16,z7,z15,z2,z132,z9]),(0,[z7,z48,z15,z210,z168,z13]),(0,[z7,z15,z2,z4,z1217,z13])],[(0,[z7,z15,z2,z3,z4,z1218]),(0,[z7,z48,z15,z2,z4,z722]),(0,[z7,z666,z2,z3,z4,z13])],[(0,[z7,z15,z2,z130,z4,z13])],[(0,[z7,z15,z2,z66,z4,z35]),(0,[z7,z15,z2,z3,z1219,z4])],[(0,[z1220,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z4,z35,z166]),(0,[z16,z7,z86,z2,z32,z4]),(0,[z249,z15,z27,z2,z4,z13]),(0,[z7,z15,z2,z3,z41,z9])],[(0,[z7,z15,z2,z3,z4,z340])],[(0,[z15,z517,z12,z3,z4,z13]),(0,[z1202,z15,z2,z3,z4,z13]),(0,[z15,z27,z2,z3,z21,z4])],[(0,[z7,z15,z27,z2,z4,z205]),(0,[z7,z15,z2,z3,z143,z9]),(0,[z10,z15,z12,z3,z4,z5]),(0,[z7,z1106,z2,z3,z4,z13])],[(0,[z7,z15,z1221,z3,z4,z13]),(0,[z48,z15,z2,z50,z4,z5]),(0,[z16,z7,z2,z8,z4,z5]),(0,[z7,z15,z2,z3,z121,z9])],[(0,[z7,z15,z2,z1222,z4,z13]),(0,[z7,z15,z2,z4,z1223,z13]),(0,[z7,z15,z2,z32,z4,z331]),(0,[z7,z15,z2,z3,z1224,z4])],[(0,[z7,z15,z2,z3,z1225,z4]),(0,[z15,z2,z3,z4,z1226,z5]),(0,[z7,z48,z15,z2,z4,z695])],[(0,[z129,z15,z2,z155,z4,z9]),(0,[z54,z7,z15,z2,z4,z5]),(0,[z7,z15,z2,z118,z4,z187])],[(0,[z7,z15,z2,z3,z1227,z9]),(0,[z15,z2,z3,z21,z4,z84])],[(0,[z7,z15,z2,z1228,z4,z13])],[(0,[z15,z1,z2,z3,z4,z389]),(0,[z416,z48,z15,z2,z4,z35]),(0,[z15,z2,z234,z3,z32,z21])],[(0,[z15,z2,z3,z4,z1229,z5]),(0,[z1230,z7,z15,z2,z4,z1231]),(0,[z7,z15,z2,z3,z4,z1232]),(0,[z46,z7,z192,z2,z4,z13]),(0,[z70,z7,z15,z4,z77,z71]),(0,[z7,z2,z32,z4,z114,z77])]],
   [[(0,[z7,z15,z2,z3,z4,z1233]),(0,[z53,z16,z7,z345,z4,z13]),(0,[z7,z1234,z15,z2,z4,z13]),(0,[z7,z15,z2,z894,z77,z13]),(0,[z7,z15,z2,z167,z4,z9])],[(0,[z7,z15,z1235,z2,z4,z13]),(0,[z1236,z48,z15,z2,z4,z13]),(0,[z53,z7,z15,z2,z34,z13])],[(0,[z7,z15,z27,z2,z4,z273]),(0,[z113,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z23,z32,z4])],[(0,[z16,z7,z471,z2,z4,z13]),(0,[z175,z7,z15,z3,z41,z9])],[(0,[z15,z2,z3,z1237,z4,z5]),(0,[z1089,z477,z15,z2,z4,z13]),(0,[z576,z15,z2,z3,z4,z1172]),(0,[z7,z15,z2,z3,z4,z695])],[],[(0,[z7,z48,z15,z2,z4,z9]),(0,[z53,z16,z59,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1238])],[(0,[z7,z15,z2,z32,z4,z284])],[(0,[z7,z15,z2,z372,z143,z13]),(0,[z7,z15,z12,z3,z222,z13]),(0,[z7,z15,z2,z3,z222,z9]),(0,[z7,z1011,z44,z2,z4,z13])],[(0,[z15,z2,z141,z130,z4,z13]),(0,[z16,z7,z1239,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z314]),(0,[z53,z16,z7,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1240]),(0,[z7,z15,z1241,z3,z4,z484])],[(0,[z7,z292,z15,z2,z4,z13]),(0,[z1236,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z1242,z3,z32])],[(0,[z91,z15,z2,z3,z4,z42]),(0,[z7,z15,z2,z4,z13,z1243]),(0,[z7,z15,z2,z1244,z4,z13])],[(0,[z7,z15,z2,z1245,z3,z156])],[(0,[z7,z15,z2,z3,z734,z9]),(0,[z15,z2,z3,z21,z1246,z4])],[(0,[z15,z2,z3,z4,z47,z5]),(0,[z7,z15,z2,z3,z4,z1247])],[(0,[z7,z15,z2,z3,z4,z9]),(0,[z7,z63,z2,z3,z4,z262])],[(0,[z7,z15,z2,z3,z1248,z4]),(0,[z7,z2,z3,z95,z563,z13]),(0,[z7,z159,z2,z193,z4,z13])],[(0,[z7,z15,z355,z100,z4,z13]),(0,[z7,z15,z2,z1249,z4,z13]),(0,[z7,z15,z2,z4,z1250,z13])],[(0,[z7,z15,z2,z3,z4,z1251]),(0,[z7,z15,z223,z2,z4,z13])],[(0,[z392,z15,z2,z3,z4,z13])],[(0,[z86,z1,z2,z3,z4,z5]),(0,[z7,z293,z2,z3,z4,z13]),(0,[z1252,z7,z15,z2,z4,z13])],[(0,[z7,z15,z1121,z3,z4,z13]),(0,[z1253,z7,z15,z2,z3,z4]),(0,[z7,z1254,z15,z2,z4,z13]),(0,[z7,z44,z2,z3,z4,z9]),(0,[z7,z15,z420,z2,z32,z4])],[(0,[z16,z7,z11,z2,z4,z13]),(0,[z725,z7,z2,z3,z4,z13]),(0,[z15,z63,z2,z3,z4,z5]),(0,[z264,z15,z2,z3,z4,z13]),(0,[z1255,z7,z15,z2,z3,z4]),(1,[z15,z2,z21,z4,z77])],[(0,[z1256,z7,z15,z2,z4,z13]),(1,[z15,z2,z3,z156,z50]),(0,[z53,z16,z7,z2,z4,z5]),(0,[z7,z48,z15,z2,z4,z1257]),(0,[z7,z15,z27,z2,z4,z446])],[(0,[z7,z15,z2,z372,z222,z13]),(0,[z49,z48,z15,z2,z50,z13]),(0,[z7,z15,z2,z3,z4,z1258]),(0,[z762,z15,z2,z4,z982,z13])],[(0,[z7,z292,z15,z2,z4,z5])],[(0,[z7,z15,z2,z1259,z4,z13]),(0,[z16,z7,z110,z2,z4,z13])],[(0,[z91,z15,z2,z4,z77,z5]),(0,[z15,z1260,z2,z3,z4,z5]),(0,[z54,z7,z15,z2,z331,z13])],[(0,[z7,z15,z2,z3,z4,z17])],[(0,[z7,z15,z2,z3,z1261,z4]),(0,[z7,z135,z2,z453,z4,z13]),(0,[z46,z7,z2,z4,z13,z1262]),(0,[z274,z7,z15,z2,z194,z4])],[(1,[z7,z15,z2,z276,z13])]],
   [[(0,[z7,z15,z2,z3,z1263,z13]),(0,[z7,z15,z1264,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z151]),(0,[z7,z15,z2,z4,z77,z103]),(0,[z7,z15,z2,z3,z1265,z4]),(0,[z15,z2,z3,z156,z21,z4]),(0,[z7,z15,z2,z4,z34,z13]),(0,[z7,z15,z2,z4,z811,z13]),(0,[z7,z15,z2,z4,z77,z119])],[(0,[z15,z2,z3,z1266,z4,z35])],[(0,[z7,z15,z223,z2,z4,z5]),(0,[z46,z7,z2,z268,z4,z13]),(0,[z7,z15,z2,z3,z4,z1257]),(0,[z7,z15,z1267,z2,z4,z13])],[(0,[z0,z15,z2,z3,z21,z4]),(0,[z49,z15,z2,z3,z50,z13]),(0,[z15,z2,z3,z268,z21,z4]),(0,[z7,z15,z3,z214,z41,z13]),(0,[z7,z15,z27,z2,z4,z935]),(0,[z1268,z15,z2,z3,z4,z218])],[(0,[z7,z293,z2,z3,z4,z5]),(0,[z139,z7,z2,z4,z77,z13]),(0,[z15,z2,z3,z885,z4,z5]),(0,[z16,z936,z15,z2,z4,z13])],[(0,[z137,z15,z2,z3,z4,z183]),(0,[z15,z149,z3,z4,z92,z13]),(0,[z7,z15,z2,z3,z4,z1269]),(0,[z7,z15,z2,z3,z4,z1270])],[(0,[z7,z15,z2,z3,z4,z1271]),(0,[z16,z7,z15,z2,z28,z4])],[],[(0,[z15,z1,z2,z3,z4,z42]),(0,[z7,z15,z27,z2,z77,z5]),(0,[z16,z37,z15,z2,z4,z13]),(0,[z7,z148,z15,z2,z970,z13])],[(0,[z7,z15,z27,z2,z615,z13]),(0,[z53,z7,z2,z330,z4,z13])],[(0,[z16,z7,z2,z268,z32,z4]),(0,[z7,z1272,z27,z2,z4,z13])],[(0,[z416,z15,z2,z3,z21,z4]),(0,[z1273,z7,z2,z4,z77,z13])],[(0,[z16,z7,z1260,z2,z4,z13]),(0,[z7,z15,z1274,z2,z4,z13]),(0,[z59,z2,z3,z4,z84,z13]),(0,[z7,z15,z355,z3,z4,z101]),(0,[z7,z15,z27,z2,z1275,z13])],[],[(0,[z7,z1276,z2,z3,z4,z13]),(0,[z137,z15,z517,z3,z4,z13]),(0,[z762,z15,z2,z4,z77,z5]),(0,[z7,z15,z27,z2,z96,z35]),(0,[z7,z15,z2,z4,z1277,z13])],[(0,[z7,z15,z192,z87,z4,z13]),(0,[z7,z94,z2,z3,z95,z13]),(0,[z7,z15,z2,z3,z1278,z13])],[(0,[z6,z7,z81,z8,z4,z13]),(0,[z7,z1037,z2,z3,z4,z13])],[(0,[z7,z15,z1279,z3,z4,z13]),(0,[z7,z15,z2,z3,z4,z1280])],[(0,[z800,z15,z138,z3,z4,z13]),(0,[z49,z15,z2,z3,z50,z5]),(0,[z281,z15,z2,z3,z4,z9]),(0,[z834,z7,z2,z3,z177,z4])],[],[(0,[z7,z15,z2,z3,z4,z1281]),(0,[z7,z15,z2,z3,z4,z1282]),(0,[z7,z15,z2,z1283,z4,z13]),(0,[z7,z15,z2,z1284,z4,z13]),(0,[z7,z15,z2,z1125,z4,z35]),(0,[z7,z15,z2,z3,z4,z1285]),(0,[z7,z15,z591,z3,z4,z160])],[(0,[z7,z15,z2,z123,z4,z35]),(0,[z7,z15,z2,z3,z4,z1286]),(0,[z7,z15,z1287,z3,z4,z617]),(0,[z7,z15,z2,z118,z4,z309])],[(0,[z7,z15,z2,z3,z4,z1288]),(0,[z7,z48,z15,z2,z32,z4])],[(0,[z7,z15,z2,z1289,z4,z13]),(0,[z139,z7,z2,z141,z4,z13]),(0,[z91,z15,z2,z3,z4,z5]),(0,[z7,z63,z2,z557,z4,z13]),(0,[z15,z2,z3,z4,z35,z520]),(0,[z7,z15,z2,z531,z4,z13])],[(0,[z15,z1,z2,z4,z77,z5]),(0,[z7,z15,z2,z3,z1290,z4]),(0,[z46,z7,z2,z1058,z4,z13])],[(0,[z7,z15,z149,z4,z77,z13]),(0,[z53,z16,z7,z2,z331,z13]),(0,[z16,z7,z2,z4,z88,z13])],[(0,[z10,z150,z12,z3,z4,z13]),(0,[z7,z48,z15,z149,z4,z13]),(0,[z6,z7,z209,z3,z4,z13]),(1,[z16,z15,z2,z21,z4]),(0,[z7,z15,z122,z2,z4,z13]),(0,[z7,z185,z2,z343,z4,z13])],[(0,[z7,z15,z2,z3,z4,z103])],[(0,[z7,z15,z2,z3,z1291,z4])],[(0,[z7,z15,z2,z3,z4,z1292]),(0,[z137,z15,z2,z3,z156,z4]),(0,[z16,z7,z86,z2,z4,z5]),(0,[z7,z15,z263,z2,z598,z4]),(0,[z7,z15,z2,z1293,z4,z13]),(0,[z7,z1294,z2,z3,z4,z13]),(0,[z7,z15,z2,z131,z4,z13]),(0,[z46,z7,z2,z96,z4,z13])],[(0,[z16,z7,z2,z207,z4,z13]),(0,[z7,z94,z2,z3,z95,z5]),(0,[z7,z15,z2,z3,z1295,z4]),(0,[z7,z185,z2,z468,z4,z13])],[(0,[z139,z7,z2,z3,z4,z13]),(0,[z7,z1296,z2,z3,z4,z13]),(0,[z15,z2,z1297,z3,z4,z5]),(0,[z7,z15,z2,z3,z4,z1298]),(0,[z7,z1299,z15,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z101]),(0,[z7,z15,z27,z650,z4,z160]),(0,[z516,z46,z7,z2,z4,z13])]],
   [[(0,[z7,z15,z2,z3,z331,z9]),(0,[z46,z7,z2,z4,z84,z13]),(0,[z7,z15,z2,z234,z3,z120]),(1,[z15,z27,z2,z21,z4])],[],[(0,[z7,z15,z27,z2,z4,z389]),(0,[z7,z15,z2,z3,z1300,z13]),(0,[z7,z15,z2,z168,z331,z13]),(0,[z7,z48,z15,z2,z168,z9]),(0,[z7,z1183,z2,z3,z4,z13]),(0,[z7,z15,z2,z234,z3,z32]),(0,[z893,z15,z2,z3,z32,z4])],[(0,[z7,z1301,z2,z3,z4,z13]),(0,[z7,z15,z2,z3,z153,z13]),(0,[z7,z15,z2,z1284,z4,z5]),(0,[z832,z48,z15,z2,z4,z13]),(0,[z7,z15,z2,z181,z4,z285])],[(0,[z7,z48,z2,z295,z4,z5]),(0,[z53,z7,z2,z3,z84,z13]),(0,[z7,z15,z2,z4,z1302,z13]),(0,[z7,z15,z2,z3,z797,z4])],[(0,[z16,z7,z537,z2,z4,z13]),(0,[z7,z15,z2,z4,z13,z1303]),(0,[z7,z789,z2,z3,z4,z13])],[(0,[z1273,z7,z2,z3,z4,z13]),(0,[z70,z7,z15,z3,z489,z4])],[(0,[z90,z48,z15,z2,z4,z5]),(0,[z59,z15,z2,z3,z4,z35]),(0,[z7,z15,z2,z3,z336,z9])],[(0,[z7,z15,z2,z3,z1015,z13]),(0,[z569,z7,z11,z2,z4,z13]),(0,[z7,z15,z2,z752,z4,z151]),(0,[z63,z2,z3,z4,z13,z5])],[(0,[z7,z15,z122,z2,z4,z5]),(0,[z762,z15,z2,z3,z4,z5])],[(0,[z7,z15,z2,z3,z4,z1304]),(0,[z15,z2,z3,z28,z21,z4]),(0,[z46,z7,z2,z4,z35,z13])],[(0,[z274,z7,z15,z2,z4,z1231]),(0,[z7,z15,z2,z32,z949,z4])],[(0,[z7,z15,z2,z131,z4,z5]),(0,[z7,z15,z2,z3,z168,z9]),(0,[z7,z15,z2,z540,z4,z77])],[(0,[z16,z225,z7,z2,z8,z4]),(0,[z7,z15,z2,z1305,z4,z13]),(0,[z1306,z15,z2,z3,z21,z4])],[(0,[z139,z7,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z1307,z9]),(0,[z7,z15,z2,z4,z187,z309])],[(0,[z7,z15,z2,z3,z1308,z4]),(0,[z54,z7,z412,z2,z4,z13]),(0,[z7,z241,z2,z4,z77,z13]),(0,[z1309,z7,z15,z2,z4,z13]),(0,[z656,z15,z2,z3,z21,z4])],[(0,[z7,z15,z2,z3,z4,z1310]),(0,[z16,z15,z2,z12,z4,z5]),(0,[z7,z15,z2,z184,z4,z13]),(0,[z7,z15,z1311,z2,z4,z13])],[(0,[z15,z2,z3,z400,z4,z5]),(0,[z161,z15,z2,z3,z21,z4]),(0,[z7,z15,z2,z3,z1312,z4]),(0,[z16,z7,z2,z598,z8,z4])],[(0,[z7,z15,z2,z4,z1313,z13]),(0,[z7,z48,z2,z4,z114,z13]),(0,[z7,z15,z192,z193,z4,z13]),(0,[z7,z15,z2,z23,z4,z446])],[(0,[z1314,z15,z2,z3,z4,z5]),(0,[z225,z7,z2,z3,z4,z78])],[],[(0,[z7,z15,z2,z32,z4,z166])],[(0,[z819,z7,z2,z3,z4,z13]),(0,[z1073,z7,z15,z2,z4,z1192])],[(0,[z182,z15,z2,z3,z4,z5]),(0,[z15,z2,z3,z244,z4,z5]),(0,[z16,z7,z1315,z2,z4,z13]),(0,[z7,z15,z418,z2,z384,z4]),(0,[z7,z574,z2,z3,z4,z13])],[(0,[z7,z110,z97,z3,z4,z13]),(0,[z7,z148,z15,z2,z34,z13]),(0,[z7,z15,z2,z508,z77,z9])],[(0,[z7,z15,z2,z3,z13,z746]),(0,[z16,z1316,z7,z2,z4,z13]),(0,[z91,z15,z2,z3,z50,z5]),(0,[z15,z2,z3,z4,z5,z1317]),(0,[z7,z15,z2,z1158,z4,z35]),(0,[z7,z15,z2,z1318,z3,z4]),(0,[z7,z15,z2,z305,z4,z77]),(0,[z7,z15,z2,z208,z4,z13])],[(0,[z7,z15,z355,z4,z77,z13])],[(0,[z16,z1319,z7,z2,z4,z13]),(0,[z7,z185,z2,z3,z4,z35])],[(0,[z15,z2,z1320,z3,z4,z5]),(0,[z7,z15,z2,z4,z13,z1321])],[(0,[z216,z7,z15,z2,z4,z13]),(0,[z7,z15,z27,z2,z4,z52]),(0,[z16,z7,z15,z1016,z4,z13]),(0,[z16,z374,z7,z2,z4,z9]),(0,[z53,z7,z2,z297,z84,z13]),(0,[z7,z15,z27,z2,z4,z55])],[(0,[z7,z2,z3,z4,z9,z629])],[(0,[z7,z15,z2,z3,z4,z1322]),(0,[z16,z7,z1,z2,z4,z35]),(0,[z7,z15,z2,z3,z32,z143]),(0,[z7,z110,z2,z3,z4,z35]),(0,[z91,z15,z2,z300,z92,z13]),(0,[z7,z15,z1323,z3,z4,z13]),(0,[z7,z15,z2,z3,z4,z1324])]],
   [[(0,[z7,z15,z2,z3,z4,z874]),(0,[z7,z15,z650,z3,z4,z1325]),(0,[z7,z15,z345,z3,z4,z35]),(0,[z542,z7,z48,z15,z2,z4]),(0,[z15,z2,z4,z77,z529,z13])],[(0,[z7,z15,z192,z193,z4,z5])],[(0,[z7,z150,z2,z3,z4,z9]),(0,[z7,z15,z2,z3,z4,z1326]),(0,[z249,z48,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z1327,z9]),(0,[z1073,z7,z15,z2,z4,z79])],[(0,[z7,z1328,z2,z3,z4,z13]),(0,[z7,z15,z2,z100,z32,z4])],[(0,[z16,z7,z15,z2,z4,z218]),(0,[z7,z15,z2,z3,z1329,z9])],[(0,[z7,z48,z15,z2,z4,z205]),(0,[z7,z15,z2,z3,z1330,z4]),(0,[z7,z15,z2,z3,z41,z314]),(0,[z46,z76,z7,z2,z4,z13]),(0,[z7,z15,z2,z4,z77,z246])],[(0,[z7,z15,z2,z1331,z4,z13])],[(0,[z7,z2,z295,z100,z4,z13]),(0,[z7,z15,z2,z1307,z77,z13]),(1,[z819,z7,z2,z4,z13])],[(0,[z7,z15,z2,z208,z4,z5]),(0,[z7,z15,z1332,z2,z4,z13]),(0,[z186,z15,z2,z343,z4,z13]),(0,[z7,z2,z3,z668,z4,z13])],[(0,[z7,z15,z2,z3,z4,z671]),(0,[z7,z1333,z15,z2,z3,z4]),(0,[z7,z15,z2,z3,z4,z1334]),(0,[z1078,z7,z15,z4,z287,z13]),(0,[z7,z15,z2,z4,z371,z79])],[(0,[z7,z241,z2,z3,z4,z13]),(0,[z7,z412,z94,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1335])],[(0,[z249,z15,z2,z3,z4,z13]),(0,[z216,z7,z15,z2,z4,z5]),(0,[z7,z15,z2,z3,z4,z1336]),(0,[z7,z15,z27,z2,z4,z42]),(0,[z7,z1337,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z1338,z4]),(0,[z7,z308,z2,z343,z4,z13]),(0,[z981,z7,z15,z2,z4,z13])],[(0,[z46,z256,z7,z2,z4,z13]),(0,[z48,z15,z2,z4,z35,z5]),(0,[z7,z15,z1287,z3,z4,z160]),(0,[z7,z86,z2,z255,z4,z13]),(0,[z7,z135,z2,z3,z4,z9]),(0,[z1339,z15,z2,z3,z4,z13]),(0,[z7,z15,z2,z1340,z4,z13])],[(0,[z7,z15,z1341,z3,z4,z1325]),(0,[z7,z15,z2,z3,z1342,z4])],[(0,[z7,z2,z3,z4,z114,z35]),(0,[z7,z15,z2,z255,z4,z13]),(0,[z15,z2,z118,z3,z21,z4])],[(0,[z7,z48,z15,z2,z4,z273]),(0,[z7,z15,z263,z2,z4,z35]),(0,[z16,z765,z15,z2,z4,z13])],[(0,[z7,z15,z2,z3,z1343,z4]),(0,[z16,z7,z345,z3,z4,z13]),(0,[z59,z15,z2,z123,z4,z13]),(0,[z15,z2,z3,z443,z21,z4])],[(0,[z7,z15,z2,z3,z4,z1344]),(0,[z7,z15,z2,z1345,z4,z13]),(0,[z7,z15,z2,z3,z4,z1346]),(0,[z6,z225,z7,z8,z3,z4])],[(0,[z7,z15,z2,z3,z4,z1347]),(0,[z46,z7,z15,z2,z4,z9])],[(0,[z7,z15,z2,z1348,z4,z13]),(0,[z7,z15,z2,z3,z41,z446])],[(0,[z7,z15,z418,z2,z4,z55]),(0,[z7,z15,z27,z2,z729,z13]),(0,[z7,z159,z2,z3,z4,z9]),(0,[z7,z15,z1349,z2,z4,z13])],[(0,[z1350,z7,z15,z2,z3,z4]),(0,[z7,z15,z1351,z3,z4,z13]),(0,[z7,z15,z149,z3,z50,z13]),(0,[z7,z15,z27,z2,z598,z4]),(0,[z576,z15,z2,z3,z4,z78]),(0,[z1352,z46,z7,z2,z4,z13])],[(0,[z46,z252,z7,z2,z4,z13]),(0,[z139,z7,z48,z2,z4,z13]),(0,[z7,z48,z15,z2,z4,z314]),(0,[z16,z7,z2,z95,z4,z13]),(0,[z46,z7,z2,z4,z13,z78]),(0,[z7,z1353,z2,z3,z4,z13])],[(0,[z129,z15,z2,z3,z21,z4]),(0,[z7,z15,z2,z3,z4,z1354]),(0,[z70,z7,z308,z3,z4,z71]),(0,[z46,z7,z27,z2,z4,z13]),(0,[z7,z15,z2,z4,z309,z79])],[(0,[z7,z15,z2,z4,z1355,z13]),(0,[z7,z1356,z2,z3,z4,z13]),(0,[z819,z7,z2,z4,z284,z13]),(0,[z7,z15,z2,z3,z32,z866])],[(0,[z7,z15,z698,z2,z4,z13]),(0,[z7,z15,z2,z3,z222,z1357]),(0,[z7,z15,z2,z3,z4,z273]),(0,[z7,z15,z2,z3,z4,z1358]),(0,[z390,z7,z15,z2,z4,z35]),(0,[z7,z8,z3,z4,z253,z13])],[(0,[z15,z2,z4,z77,z35,z5]),(0,[z249,z15,z2,z3,z4,z5]),(1,[z53,z7,z2,z331,z13]),(0,[z576,z15,z2,z4,z77,z13]),(0,[z7,z15,z2,z3,z194,z9])],[(0,[z53,z7,z48,z2,z84,z13]),(0,[z7,z15,z2,z1359,z4,z13]),(0,[z1360,z46,z7,z2,z4,z13])],[(0,[z49,z15,z2,z3,z4,z218]),(0,[z7,z15,z2,z3,z280,z13]),(0,[z7,z15,z2,z3,z32,z254]),(0,[z7,z15,z2,z4,z1361,z13])],[(0,[z137,z15,z1362,z3,z4,z13]),(0,[z7,z15,z2,z255,z4,z5]),(0,[z1363,z15,z2,z3,z4,z5]),(0,[z16,z576,z15,z2,z4,z13])],[(0,[z7,z15,z2,z3,z143,z151]),(0,[z15,z2,z1364,z3,z4,z5]),(0,[z7,z15,z2,z3,z1365,z4]),(0,[z16,z203,z15,z2,z4,z13]),(0,[z16,z7,z15,z2,z234,z32]),(0,[z7,z15,z210,z168,z77,z13]),(0,[z15,z2,z234,z3,z21,z4])]],
   [[(0,[z7,z48,z15,z707,z4,z13]),(0,[z7,z15,z2,z3,z4,z246]),(0,[z15,z2,z3,z21,z4,z160]),(0,[z15,z2,z180,z3,z21,z4]),(0,[z388,z7,z2,z3,z4,z9])],[(0,[z7,z15,z2,z3,z4,z314]),(0,[z1366,z7,z15,z3,z4,z500]),(0,[z94,z15,z2,z3,z21,z4])],[(0,[z7,z15,z138,z3,z222,z13]),(0,[z7,z15,z2,z3,z4,z1357]),(0,[z1367,z7,z15,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1368])],[(0,[z1369,z7,z8,z3,z4,z13]),(0,[z7,z15,z2,z196,z4,z77])],[(0,[z7,z15,z1370,z2,z143,z13]),(0,[z7,z293,z2,z3,z4,z383]),(0,[z16,z7,z261,z2,z4,z13]),(0,[z1371,z7,z15,z2,z3,z4]),(0,[z7,z1372,z15,z2,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1373]),(0,[z140,z15,z27,z2,z4,z5]),(0,[z7,z15,z2,z1374,z4,z13]),(0,[z186,z308,z2,z3,z4,z13])],[(0,[z7,z1375,z2,z3,z4,z13]),(0,[z16,z7,z2,z95,z4,z5]),(0,[z16,z7,z86,z57,z4,z13]),(0,[z7,z48,z15,z2,z4,z446])],[(0,[z15,z2,z130,z155,z4,z13])],[(0,[z7,z15,z2,z1376,z4,z13]),(0,[z7,z15,z2,z330,z4,z35]),(0,[z7,z15,z1377,z3,z4,z13]),(0,[z7,z15,z2,z131,z508,z9])],[(0,[z7,z15,z2,z3,z4,z1378]),(0,[z7,z15,z2,z300,z4,z13])],[(0,[z1,z2,z8,z3,z4,z5]),(0,[z7,z15,z345,z123,z4,z13]),(0,[z7,z15,z2,z440,z4,z9]),(0,[z7,z15,z27,z2,z4,z24])],[(0,[z7,z15,z2,z1379,z4,z13]),(0,[z133,z15,z2,z4,z77,z13])],[(0,[z7,z15,z2,z3,z4,z322]),(0,[z7,z15,z2,z1380,z4,z13]),(0,[z7,z15,z27,z2,z196,z4])],[(0,[z1209,z7,z15,z2,z4,z35]),(0,[z76,z7,z2,z3,z177,z4])],[(0,[z7,z48,z15,z2,z4,z151]),(0,[z7,z15,z2,z3,z1381,z13]),(0,[z7,z44,z27,z2,z4,z13])],[(0,[z7,z15,z2,z1382,z4,z13]),(0,[z10,z15,z12,z3,z4,z35]),(0,[z15,z2,z8,z3,z21,z4]),(0,[z7,z15,z2,z380,z32,z4])],[(0,[z7,z15,z2,z3,z222,z151]),(0,[z7,z15,z1383,z2,z4,z13]),(0,[z16,z7,z2,z8,z4,z35]),(0,[z405,z7,z15,z58,z32,z4])],[(0,[z867,z15,z2,z3,z4,z5]),(0,[z7,z345,z3,z4,z84,z13])],[(0,[z7,z15,z2,z1384,z4,z13]),(0,[z203,z15,z2,z3,z4,z1143])],[(0,[z54,z7,z15,z2,z4,z35]),(0,[z7,z15,z2,z4,z13,z1385]),(0,[z7,z15,z2,z3,z4,z1386])],[(0,[z49,z15,z2,z3,z50,z189]),(0,[z7,z15,z2,z4,z331,z9])],[(0,[z7,z15,z2,z4,z783,z13]),(0,[z6,z7,z48,z8,z4,z13]),(0,[z692,z15,z2,z3,z4,z13])],[(0,[z252,z48,z1,z2,z4,z13]),(0,[z16,z161,z1,z2,z4,z13]),(0,[z7,z15,z2,z3,z4,z1387]),(0,[z7,z15,z2,z3,z4,z1388]),(0,[z7,z15,z2,z343,z4,z9])],[],[(0,[z252,z1,z2,z3,z4,z340]),(0,[z7,z15,z2,z3,z4,z151]),(0,[z7,z15,z2,z300,z4,z5]),(0,[z15,z2,z3,z4,z1389,z5])],[(0,[z46,z416,z7,z2,z4,z13]),(0,[z16,z7,z15,z2,z41,z9]),(0,[z304,z15,z2,z4,z77,z13])],[(0,[z16,z7,z15,z2,z4,z340]),(0,[z15,z2,z50,z4,z77,z5]),(0,[z7,z15,z2,z468,z4,z9])],[],[(0,[z781,z7,z15,z3,z4,z1390]),(0,[z7,z148,z15,z2,z4,z9]),(0,[z59,z15,z345,z3,z4,z13])],[(0,[z7,z15,z1370,z2,z4,z13]),(0,[z7,z15,z2,z557,z32,z4]),(0,[z7,z15,z2,z3,z4,z1391])],[(0,[z7,z15,z223,z2,z244,z4])],[]],
   [[(0,[z16,z7,z15,z1392,z4,z13]),(0,[z113,z15,z27,z2,z4,z13]),(0,[z304,z15,z2,z118,z3,z4]),(0,[z200,z7,z15,z27,z2,z4])],[(1,[z7,z15,z2,z77,z314]),(0,[z7,z15,z2,z3,z4,z1393])],[(0,[z16,z252,z1,z2,z4,z13]),(0,[z16,z1,z2,z4,z92,z13]),(0,[z7,z15,z2,z3,z1394,z4]),(0,[z7,z1272,z2,z3,z4,z13])],[(0,[z7,z15,z2,z4,z284,z246]),(0,[z46,z7,z15,z2,z32,z4])],[(0,[z16,z7,z15,z2,z4,z1232])],[(0,[z7,z15,z2,z3,z4,z1395]),(0,[z137,z15,z27,z2,z4,z5])],[(0,[z1089,z15,z2,z155,z4,z13]),(0,[z133,z15,z2,z3,z4,z13])],[(0,[z46,z7,z2,z12,z4,z13]),(0,[z7,z15,z2,z3,z4,z38]),(0,[z15,z2,z3,z4,z35,z1396])],[(0,[z7,z15,z2,z568,z3,z32]),(0,[z7,z15,z2,z379,z4,z13]),(0,[z15,z589,z2,z3,z21,z4]),(0,[z37,z15,z27,z2,z4,z13]),(0,[z7,z15,z2,z1397,z4,z13])],[(0,[z15,z2,z3,z4,z1398,z5]),(0,[z16,z7,z15,z2,z4,z695]),(0,[z7,z15,z317,z3,z4,z13])],[],[(0,[z15,z12,z3,z4,z1325,z5]),(0,[z7,z15,z2,z3,z381,z13]),(0,[z16,z7,z15,z2,z4,z1238]),(0,[z46,z7,z2,z32,z4,z13])],[(0,[z7,z15,z2,z3,z4,z1399]),(0,[z7,z15,z2,z3,z1400,z4])],[(0,[z16,z161,z7,z2,z4,z13]),(0,[z7,z15,z2,z4,z77,z40]),(0,[z7,z15,z2,z3,z1401,z9]),(0,[z16,z7,z2,z4,z13,z1139]),(0,[z7,z48,z15,z2,z4,z101]),(0,[z7,z48,z15,z650,z4,z160]),(0,[z7,z2,z330,z95,z4,z13]),(0,[z7,z15,z2,z3,z4,z1402]),(0,[z7,z15,z2,z1058,z385,z4]),(0,[z7,z15,z591,z3,z443,z4])],[(0,[z139,z7,z2,z3,z4,z383]),(0,[z53,z16,z7,z355,z4,z13]),(1,[z48,z15,z2,z21,z4]),(0,[z7,z15,z2,z1403,z4,z13])],[(0,[z882,z7,z2,z3,z84,z13]),(0,[z7,z15,z1404,z3,z4,z13]),(0,[z7,z15,z2,z4,z35,z238]),(0,[z7,z15,z1392,z3,z4,z13]),(0,[z1405,z7,z15,z2,z3,z4])],[(0,[z7,z48,z15,z2,z4,z389]),(0,[z7,z15,z2,z3,z1406,z13]),(0,[z7,z15,z97,z3,z4,z9]),(0,[z19,z7,z15,z2,z4,z13]),(0,[z15,z1407,z2,z3,z4,z5]),(0,[z53,z16,z7,z2,z4,z35]),(0,[z7,z15,z2,z3,z1408,z4])],[(0,[z7,z15,z2,z3,z4,z1409]),(0,[z7,z15,z2,z3,z4,z1410]),(0,[z7,z2,z4,z1021,z284,z13]),(0,[z7,z15,z2,z4,z77,z56])],[(0,[z7,z292,z15,z2,z4,z35]),(0,[z7,z15,z2,z3,z4,z1411]),(0,[z7,z15,z2,z3,z663,z42]),(0,[z7,z15,z2,z3,z1412,z4]),(0,[z1413,z15,z2,z3,z4,z13])],[(0,[z252,z1,z2,z3,z4,z9]),(0,[z161,z7,z2,z4,z331,z13]),(0,[z7,z15,z2,z3,z1414,z4])],[(0,[z304,z15,z2,z3,z4,z13])],[(0,[z1415,z15,z2,z3,z4,z5]),(0,[z16,z7,z15,z2,z4,z9]),(0,[z175,z7,z15,z23,z41,z13]),(0,[z7,z15,z1416,z2,z4,z13])],[],[(0,[z7,z15,z2,z3,z4,z1417]),(0,[z7,z15,z2,z379,z4,z5]),(0,[z46,z7,z2,z58,z4,z13]),(0,[z15,z2,z3,z21,z4,z41])],[(0,[z7,z15,z2,z3,z4,z1418]),(1,[z19,z7,z2,z4,z13]),(0,[z54,z7,z86,z2,z4,z13]),(0,[z7,z94,z15,z2,z331,z13]),(0,[z7,z15,z27,z2,z331,z13])],[(0,[z7,z15,z2,z3,z41,z52]),(0,[z1419,z147,z15,z2,z4,z13]),(0,[z7,z15,z2,z395,z77,z13])],[(0,[z7,z15,z2,z3,z4,z389]),(0,[z91,z15,z2,z3,z92,z42]),(0,[z7,z15,z223,z2,z4,z35]),(0,[z1420,z15,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z1421,z9]),(0,[z7,z15,z2,z440,z32,z4])],[(0,[z7,z15,z2,z1422,z4,z13]),(0,[z1423,z15,z2,z3,z4,z13])],[(0,[z16,z161,z7,z2,z4,z5]),(0,[z7,z293,z2,z3,z4,z35]),(0,[z15,z2,z3,z50,z41,z5]),(0,[z15,z2,z3,z4,z5,z500]),(0,[z7,z15,z2,z32,z4,z419])],[(0,[z7,z15,z2,z3,z168,z314]),(0,[z7,z15,z210,z168,z284,z13]),(0,[z15,z2,z662,z3,z21,z4])],[(0,[z7,z15,z2,z662,z4,z187]),(0,[z7,z15,z2,z1424,z4,z13])],[(0,[z7,z15,z2,z300,z4,z262]),(0,[z16,z7,z2,z1425,z4,z13]),(0,[z46,z7,z2,z4,z114,z13])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z139,z2,z130,z4,z13]),(0,[z19,z7,z2,z4,z9]),(0,[z46,z7,z2,z4,z314]),(0,[z37,z15,z453,z41,z13]),(0,[z7,z15,z3,z4,z480]),(0,[z15,z2,z1426,z21,z4])],[(0,[z15,z27,z149,z4,z5]),(0,[z823,z15,z2,z4,z5]),(0,[z7,z15,z2,z4,z1427]),(0,[z264,z15,z263,z2,z4]),(0,[z522,z7,z15,z4,z71]),(0,[z7,z345,z3,z84,z119]),(0,[z37,z15,z23,z41,z13])],[(0,[z15,z2,z130,z4,z35]),(0,[z15,z2,z156,z50,z77]),(0,[z46,z7,z2,z32,z4]),(0,[z37,z15,z3,z32,z41]),(0,[z1428,z15,z27,z2,z4])],[(0,[z46,z7,z2,z1154,z13]),(0,[z882,z15,z2,z3,z42]),(0,[z7,z15,z2,z77,z603]),(0,[z48,z15,z2,z156,z50])],[(0,[z15,z2,z4,z77,z520]),(0,[z16,z7,z345,z4,z119]),(0,[z46,z7,z2,z305,z4])],[(0,[z15,z2,z3,z28,z74]),(0,[z7,z2,z267,z4,z9]),(0,[z1429,z7,z2,z4,z13])],[(0,[z15,z471,z2,z4,z5]),(0,[z46,z7,z2,z35,z314]),(0,[z15,z81,z2,z21,z4]),(0,[z46,z7,z2,z21,z4])],[(0,[z7,z15,z3,z214,z5])]],
   [[(0,[z11,z12,z3,z222,z13]),(0,[z7,z2,z8,z331,z9]),(0,[z37,z48,z15,z41,z13]),(0,[z7,z2,z330,z563,z13]),(0,[z46,z7,z2,z4,z56])],[(0,[z15,z12,z3,z222,z151]),(0,[z16,z1236,z2,z4,z13]),(0,[z7,z15,z3,z120,z214]),(0,[z46,z7,z707,z4,z13])],[(0,[z15,z2,z557,z21,z4]),(0,[z46,z7,z2,z568,z35]),(0,[z7,z8,z3,z253,z9]),(0,[z16,z59,z2,z132,z13]),(0,[z16,z15,z2,z1430,z4]),(0,[z16,z59,z2,z4,z119])],[],[(0,[z15,z149,z3,z92,z42]),(0,[z16,z59,z2,z4,z101])],[(0,[z16,z1,z2,z4,z5]),(0,[z63,z2,z3,z21,z4]),(0,[z15,z2,z3,z1431,z74]),(0,[z15,z2,z3,z74,z183]),(0,[z7,z86,z290,z4,z13]),(0,[z15,z2,z3,z1432,z168])],[(0,[z882,z2,z3,z84,z5]),(0,[z15,z517,z3,z4,z40]),(0,[z710,z63,z2,z4,z5]),(0,[z48,z15,z149,z92,z13]),(0,[z15,z2,z3,z74,z52]),(0,[z59,z15,z2,z3,z314]),(0,[z7,z15,z2,z419,z314])],[(0,[z53,z16,z7,z2,z314]),(0,[z16,z7,z15,z4,z480]),(0,[z46,z7,z2,z4,z446]),(0,[z1433,z7,z2,z4,z13]),(0,[z296,z7,z364,z4,z13])]],
   [[(0,[z1256,z15,z2,z4,z5]),(0,[z407,z7,z2,z331,z13]),(0,[z7,z15,z2,z280,z335])],[(0,[z7,z15,z2,z3,z1434]),(0,[z15,z2,z21,z4,z34])],[(0,[z16,z59,z2,z4,z13]),(0,[z1220,z15,z2,z4,z5]),(0,[z15,z149,z300,z4,z5]),(0,[z7,z15,z2,z100,z314]),(0,[z728,z7,z2,z331,z13]),(0,[z37,z15,z3,z41,z446]),(0,[z7,z185,z3,z4,z480]),(0,[z46,z7,z2,z4,z535])],[(0,[z15,z2,z100,z21,z4]),(0,[z7,z15,z317,z305,z4])],[(0,[z1,z2,z481,z77,z13]),(0,[z237,z2,z3,z4,z5]),(0,[z908,z16,z7,z2,z13]),(0,[z15,z2,z4,z494,z5]),(0,[z15,z2,z330,z21,z4]),(0,[z7,z15,z27,z2,z732]),(0,[z7,z15,z2,z276,z13]),(0,[z46,z7,z2,z4,z1435]),(0,[z46,z133,z2,z4,z13])],[(0,[z16,z471,z2,z4,z5]),(0,[z53,z7,z355,z331,z13]),(0,[z16,z37,z15,z41,z13]),(0,[z7,z2,z563,z77,z13])],[(0,[z7,z355,z3,z563,z13])],[(0,[z46,z7,z2,z4,z151]),(0,[z53,z7,z2,z331,z35]),(0,[z46,z7,z15,z2,z314]),(0,[z46,z2,z366,z4,z13])]],
   [[(0,[z15,z12,z3,z222,z35]),(0,[z46,z137,z2,z4,z5]),(0,[z7,z15,z2,z276,z695])],[(0,[z7,z2,z331,z1139,z9]),(0,[z7,z345,z3,z84,z9]),(0,[z304,z15,z3,z215,z71])],[(0,[z1,z2,z331,z92,z13]),(0,[z16,z2,z587,z95,z4]),(0,[z46,z7,z2,z120,z4])],[(0,[z46,z0,z2,z4,z5]),(0,[z1436,z7,z2,z4,z13]),(0,[z7,z2,z345,z331,z13]),(0,[z46,z7,z2,z970,z13]),(0,[z37,z44,z3,z41,z13]),(0,[z46,z7,z2,z4,z1437])],[(0,[z15,z12,z3,z4,z874]),(0,[z16,z7,z345,z4,z9]),(0,[z15,z2,z3,z1438,z4])],[(0,[z15,z2,z3,z74,z42]),(0,[z16,z2,z21,z177,z4])],[(0,[z63,z2,z300,z4,z5])],[(0,[z15,z1144,z3,z4,z5]),(0,[z15,z2,z3,z4,z520]),(0,[z7,z2,z1439,z331,z13]),(0,[z7,z2,z3,z563,z119]),(0,[z46,z203,z2,z4,z13]),(0,[z7,z15,z2,z1440,z4])]],
   [[(0,[z11,z517,z3,z4,z13]),(0,[z7,z15,z2,z792,z314]),(0,[z7,z345,z84,z77,z13]),(0,[z7,z15,z2,z276,z212]),(0,[z15,z2,z1441,z4,z13])],[(0,[z16,z59,z2,z4,z5]),(0,[z542,z7,z15,z317,z4])],[(0,[z16,z59,z2,z4,z9]),(0,[z819,z7,z2,z32,z4])],[(0,[z46,z7,z2,z143,z13]),(0,[z15,z2,z3,z156,z1442]),(0,[z7,z15,z2,z276,z5]),(0,[z16,z1255,z7,z2,z4]),(0,[z175,z46,z7,z41,z13])],[(0,[z16,z328,z2,z4,z5]),(0,[z46,z7,z355,z4,z13]),(0,[z46,z7,z2,z121,z13]),(0,[z7,z15,z2,z276,z9]),(0,[z46,z2,z32,z21,z4]),(0,[z412,z15,z2,z21,z4])],[(0,[z15,z517,z3,z4,z33]),(0,[z7,z15,z345,z331,z13]),(0,[z46,z1443,z2,z4,z13])],[(0,[z15,z2,z3,z895,z50]),(0,[z46,z7,z2,z4,z35]),(0,[z15,z2,z21,z297,z4])],[(0,[z15,z1404,z3,z4,z5]),(0,[z16,z7,z2,z4,z245]),(0,[z15,z2,z531,z21,z4]),(0,[z15,z2,z21,z4,z792])]],
   [[(0,[z15,z149,z3,z92,z13]),(0,[z7,z15,z1444,z4,z13]),(0,[z15,z2,z587,z4,z77])],[(0,[z15,z698,z12,z222,z13]),(0,[z37,z15,z3,z41,z35]),(0,[z7,z2,z4,z1439,z13]),(0,[z374,z7,z2,z331,z9]),(0,[z37,z15,z3,z41,z38]),(0,[z7,z15,z2,z276,z198]),(0,[z46,z7,z813,z4,z13]),(0,[z15,z2,z1188,z1203,z4])],[(0,[z15,z2,z3,z4,z1445]),(0,[z15,z12,z222,z77,z13]),(0,[z15,z122,z2,z797,z4])],[(0,[z15,z517,z4,z77,z13]),(0,[z7,z48,z15,z2,z336]),(0,[z281,z15,z3,z41,z13])],[(0,[z15,z2,z180,z21,z77])],[(0,[z46,z7,z2,z481,z13]),(0,[z1446,z7,z2,z143,z13])],[],[(0,[z16,z15,z2,z797,z4])]],
   [[(0,[z46,z49,z2,z50,z13]),(0,[z15,z2,z156,z50,z351]),(0,[z1447,z15,z2,z3,z4]),(0,[z7,z15,z2,z821,z77]),(0,[z46,z7,z2,z41,z9]),(0,[z46,z2,z4,z529,z13])],[(0,[z46,z7,z2,z4,z205])],[],[(0,[z46,z7,z345,z4,z13]),(0,[z7,z2,z3,z384,z563]),(0,[z133,z15,z2,z3,z336])],[(0,[z46,z1,z2,z4,z5]),(0,[z46,z7,z2,z222,z13]),(0,[z54,z15,z2,z21,z4])],[(0,[z7,z2,z267,z32,z4]),(0,[z46,z113,z2,z4,z13]),(0,[z15,z27,z2,z797,z4]),(0,[z15,z2,z3,z21,z121])],[(0,[z67,z15,z696,z4,z13]),(0,[z46,z7,z650,z4,z160])],[(0,[z1448,z7,z2,z4,z13]),(0,[z15,z149,z3,z92,z5])]],
   [[(0,[z1,z2,z510,z4,z5]),(0,[z15,z149,z3,z92,z9]),(0,[z16,z264,z2,z8,z4]),(0,[z15,z2,z3,z1449,z4])],[(0,[z46,z7,z2,z4,z389]),(0,[z15,z2,z3,z74,z13]),(0,[z53,z16,z2,z21,z4]),(0,[z1450,z15,z2,z4,z13]),(0,[z44,z2,z3,z21,z4])],[(0,[z882,z16,z2,z92,z13]),(0,[z16,z7,z1082,z4,z13]),(0,[z15,z2,z21,z4,z351]),(0,[z819,z7,z2,z120,z4])],[(0,[z7,z15,z3,z214,z13])],[(0,[z15,z2,z66,z21,z4]),(0,[z1451,z15,z2,z3,z4]),(0,[z16,z7,z345,z331,z13]),(0,[z46,z7,z2,z540,z4])],[(0,[z1452,z7,z2,z4,z13]),(0,[z15,z12,z3,z222,z5]),(0,[z1453,z15,z2,z4,z13]),(0,[z390,z15,z2,z21,z4]),(0,[z7,z15,z3,z214,z24])],[(0,[z16,z15,z149,z4,z5]),(0,[z7,z15,z3,z489,z215])],[(0,[z16,z249,z345,z4,z13]),(0,[z15,z2,z380,z21,z4])]],
   [[(0,[z15,z2,z3,z4,z1454])],[(0,[z15,z12,z3,z41,z42]),(0,[z63,z2,z92,z77,z13]),(0,[z16,z2,z21,z95,z4]),(0,[z7,z418,z2,z563,z13])],[(0,[z16,z161,z2,z21,z4]),(0,[z150,z2,z3,z21,z4]),(0,[z15,z149,z557,z92,z13]),(0,[z16,z59,z2,z331,z13]),(0,[z304,z15,z3,z4,z480])],[(0,[z7,z15,z3,z362,z41])],[(0,[z15,z149,z3,z21,z4]),(0,[z59,z2,z3,z563,z13])],[(0,[z62,z63,z2,z4,z5]),(0,[z63,z149,z3,z92,z13]),(0,[z15,z2,z21,z4,z331]),(0,[z7,z15,z2,z220,z9]),(0,[z46,z1455,z2,z4,z13])],[(0,[z15,z517,z3,z4,z13]),(0,[z1446,z7,z2,z4,z13]),(0,[z15,z223,z2,z21,z4]),(0,[z7,z15,z2,z331,z52]),(0,[z819,z7,z2,z4,z35]),(1,[z59,z2,z331,z13])],[(0,[z46,z7,z2,z4,z40]),(0,[z19,z2,z50,z4,z5]),(0,[z53,z7,z2,z1439,z13]),(0,[z7,z15,z77,z214,z13]),(0,[z7,z15,z468,z4,z480])]],
   [[(0,[z15,z27,z517,z4,z13]),(0,[z293,z2,z3,z21,z4]),(0,[z15,z2,z3,z74,z5]),(0,[z15,z2,z3,z4,z1442]),(0,[z46,z7,z2,z4,z1456])],[(0,[z1457,z7,z2,z4,z13]),(0,[z15,z2,z3,z74,z9]),(0,[z91,z46,z2,z92,z13]),(0,[z15,z2,z208,z21,z4])],[(0,[z15,z149,z3,z74,z13]),(0,[z15,z2,z3,z32,z74]),(0,[z15,z2,z50,z331,z5]),(0,[z16,z7,z15,z214,z13]),(0,[z48,z15,z2,z587,z4])],[(0,[z46,z7,z2,z4,z5]),(0,[z46,z2,z4,z35,z5]),(0,[z7,z15,z1016,z4,z335]),(0,[z46,z7,z2,z34,z13]),(0,[z7,z15,z317,z4,z13]),(0,[z7,z15,z3,z214,z9]),(0,[z15,z2,z21,z4,z419])],[(0,[z15,z223,z2,z74,z13]),(0,[z16,z1458,z15,z2,z4]),(0,[z16,z7,z345,z32,z4]),(0,[z7,z2,z1459,z4,z13])],[(0,[z15,z2,z568,z77,z5]),(0,[z7,z1460,z3,z4,z13]),(0,[z7,z86,z2,z331,z9]),(0,[z15,z418,z2,z21,z4]),(0,[z15,z2,z1461,z21,z4])],[(0,[z15,z149,z3,z4,z183]),(0,[z37,z15,z3,z41,z5]),(0,[z7,z345,z4,z331,z13]),(0,[z46,z7,z2,z4,z1462])],[(0,[z7,z63,z2,z77,z9]),(0,[z15,z2,z21,z4,z77]),(0,[z304,z15,z3,z4,z500]),(0,[z53,z7,z2,z811,z13]),(0,[z576,z15,z2,z3,z746]),(0,[z7,z15,z3,z215,z480]),(0,[z46,z7,z2,z526,z13])]],
   [[(0,[z16,z2,z524,z4,z5]),(0,[z16,z2,z207,z4,z5]),(0,[z15,z12,z3,z222,z33]),(0,[z15,z2,z3,z156,z50]),(0,[z46,z7,z2,z4,z957]),(0,[z46,z7,z1463,z4,z13])],[(0,[z16,z261,z2,z21,z4]),(0,[z46,z7,z2,z4,z198])],[(0,[z15,z2,z3,z1464,z13]),(0,[z15,z2,z3,z244,z74]),(0,[z59,z2,z330,z4,z13]),(0,[z46,z7,z2,z276,z13])],[(0,[z15,z2,z557,z74,z13]),(0,[z46,z7,z2,z4,z183]),(0,[z46,z7,z2,z13,z314]),(0,[z7,z2,z95,z331,z9]),(0,[z186,z15,z3,z4,z480])],[(0,[z15,z2,z3,z587,z4]),(0,[z15,z2,z372,z21,z4]),(0,[z7,z15,z3,z1465,z13]),(0,[z46,z7,z97,z4,z13]),(0,[z46,z7,z2,z4,z52]),(0,[z46,z7,z2,z4,z55])],[(0,[z46,z137,z138,z4,z13]),(0,[z48,z63,z2,z4,z5]),(0,[z7,z15,z2,z331,z42]),(0,[z46,z416,z2,z4,z35])],[(0,[z63,z2,z3,z74,z13])],[(0,[z1,z263,z2,z4,z5]),(0,[z16,z537,z2,z4,z5]),(1,[z46,z7,z2,z314]),(0,[z16,z7,z8,z41,z9])]],
   [[(0,[z16,z332,z2,z4,z5])],[(0,[z1466,z7,z2,z4,z13]),(0,[z7,z15,z2,z77,z357]),(0,[z7,z2,z267,z4,z35]),(0,[z7,z44,z453,z41,z13]),(0,[z46,z7,z2,z234,z32])],[(0,[z63,z2,z3,z4,z183]),(0,[z7,z15,z317,z4,z5]),(0,[z7,z2,z1467,z4,z13]),(0,[z241,z2,z3,z21,z4])],[(0,[z15,z2,z130,z4,z13]),(0,[z264,z308,z2,z3,z4]),(0,[z15,z2,z1468,z21,z4])],[(0,[z15,z2,z21,z4,z238]),(0,[z1428,z15,z2,z3,z4])],[],[(0,[z46,z7,z2,z4,z33]),(0,[z15,z149,z3,z28,z92]),(0,[z15,z149,z3,z92,z262]),(0,[z16,z15,z2,z4,z520]),(0,[z1433,z7,z2,z215,z13]),(0,[z2,z3,z21,z1469,z4])],[(0,[z15,z2,z255,z21,z4]),(0,[z7,z15,z410,z3,z215])]],
   [[(0,[z15,z149,z3,z32,z92]),(0,[z15,z2,z3,z21,z314]),(0,[z264,z15,z27,z2,z4]),(0,[z133,z15,z2,z77,z9]),(0,[z2,z3,z21,z4,z114])],[(0,[z7,z15,z420,z2,z336])],[(0,[z48,z15,z12,z222,z13]),(0,[z15,z2,z699,z21,z4])],[(0,[z15,z149,z3,z92,z103]),(0,[z896,z15,z2,z4,z5]),(0,[z46,z7,z2,z4,z42]),(0,[z15,z223,z2,z156,z50]),(0,[z46,z225,z7,z2,z4]),(0,[z46,z7,z2,z894,z13])],[(0,[z15,z27,z2,z4,z520]),(0,[z16,z25,z2,z4,z13]),(0,[z15,z1470,z2,z21,z4])],[(0,[z46,z2,z12,z4,z5]),(0,[z15,z355,z3,z21,z4]),(0,[z7,z15,z3,z1471,z4])],[(0,[z15,z149,z3,z156,z4]),(0,[z1472,z7,z2,z4,z13]),(0,[z46,z7,z2,z95,z9])],[(0,[z53,z7,z345,z331,z13]),(0,[z1473,z2,z3,z21,z4]),(0,[z251,z15,z2,z1246,z4])]],
   [[(0,[z48,z2,z295,z21,z4])],[(0,[z15,z12,z222,z868,z13]),(0,[z7,z15,z149,z77,z9]),(0,[z7,z15,z2,z1474,z13]),(0,[z7,z15,z2,z331,z119]),(0,[z59,z345,z3,z84,z13]),(0,[z7,z2,z4,z1475,z13])],[(0,[z15,z2,z130,z4,z5]),(0,[z63,z2,z3,z4,z42]),(0,[z53,z7,z2,z331,z101]),(0,[z15,z2,z440,z21,z4])],[(0,[z1095,z7,z2,z331,z13]),(0,[z15,z2,z130,z4,z9]),(0,[z819,z7,z2,z4,z5]),(0,[z46,z7,z2,z156,z4]),(0,[z7,z15,z87,z4,z873]),(0,[z7,z44,z3,z41,z446])],[(0,[z16,z14,z2,z4,z13])],[(0,[z53,z59,z2,z331,z13]),(0,[z7,z159,z677,z4,z13]),(0,[z7,z135,z3,z214,z13]),(0,[z15,z122,z2,z21,z4])],[(0,[z7,z15,z2,z77,z1062])],[(0,[z1,z2,z330,z4,z5]),(0,[z1476,z7,z2,z4,z13]),(0,[z15,z2,z3,z74,z262]),(0,[z49,z15,z2,z77,z218]),(0,[z7,z8,z253,z77,z13])]],
   [[(0,[z16,z7,z345,z4,z35]),(0,[z53,z7,z2,z331,z13]),(0,[z7,z308,z468,z4,z71]),(0,[z15,z2,z131,z21,z4])],[(0,[z15,z12,z3,z222,z13]),(0,[z15,z188,z2,z4,z5]),(0,[z16,z625,z2,z4,z5]),(0,[z46,z7,z2,z4,z941])],[(0,[z63,z2,z3,z156,z4]),(0,[z46,z7,z2,z4,z262]),(0,[z16,z15,z2,z21,z4]),(0,[z7,z148,z15,z2,z314]),(0,[z7,z15,z122,z214,z13]),(0,[z1071,z15,z3,z444,z4])],[(0,[z216,z15,z2,z21,z4]),(0,[z19,z7,z2,z32,z4]),(0,[z16,z125,z2,z4,z13]),(0,[z46,z1236,z2,z4,z13])],[(0,[z46,z7,z2,z4,z340]),(0,[z15,z2,z3,z156,z361]),(0,[z15,z2,z3,z74,z103]),(0,[z7,z15,z87,z526,z13]),(0,[z16,z2,z268,z21,z4])],[],[(0,[z7,z15,z2,z3,z1477]),(0,[z83,z16,z7,z41,z13]),(0,[z15,z2,z343,z21,z4])],[(0,[z46,z7,z2,z4,z103]),(0,[z7,z15,z2,z331,z1238]),(0,[z7,z15,z2,z4,z1478]),(0,[z46,z7,z2,z4,z119]),(0,[z7,z15,z2,z131,z336])]],
   [[(0,[z15,z149,z92,z77,z13]),(0,[z15,z27,z2,z21,z4]),(0,[z7,z15,z3,z214,z246]),(0,[z7,z308,z3,z215,z71])],[(0,[z15,z2,z300,z21,z4]),(0,[z46,z7,z2,z4,z101]),(0,[z7,z2,z3,z32,z563]),(0,[z46,z7,z2,z384,z4]),(0,[z46,z513,z2,z4,z13])],[(0,[z15,z517,z3,z4,z401]),(0,[z63,z2,z4,z77,z5]),(0,[z63,z2,z300,z92,z13]),(0,[z16,z224,z2,z4,z13]),(0,[z15,z2,z468,z21,z4]),(0,[z15,z2,z3,z21,z215]),(0,[z1479,z46,z7,z2,z4])],[(0,[z19,z7,z2,z244,z4]),(0,[z15,z2,z3,z1480,z4]),(0,[z37,z15,z27,z41,z13])],[(0,[z576,z2,z3,z4,z191]),(0,[z1255,z7,z15,z3,z41]),(0,[z46,z59,z2,z4,z13]),(0,[z148,z15,z2,z21,z4]),(0,[z390,z7,z2,z4,z116])],[(0,[z7,z15,z2,z331,z212])],[(0,[z15,z27,z2,z74,z13]),(0,[z281,z15,z3,z41,z9])],[(0,[z46,z7,z2,z4,z13]),(0,[z15,z1082,z3,z92,z13]),(0,[z53,z7,z2,z331,z5])]],
   [[(0,[z46,z542,z7,z2,z4]),(0,[z46,z2,z21,z4,z13])],[(0,[z15,z2,z229,z3,z5]),(0,[z15,z12,z3,z222,z9]),(0,[z16,z1260,z2,z4,z5]),(0,[z7,z15,z2,z331,z9]),(0,[z46,z7,z2,z4,z24]),(1,[z46,z2,z21,z4]),(0,[z15,z27,z2,z21,z96])],[(0,[z37,z15,z3,z41,z13])],[(0,[z46,z7,z2,z253,z13]),(0,[z46,z7,z1481,z4,z13]),(0,[z2,z21,z4,z114,z77]),(0,[z46,z7,z2,z4,z695]),(0,[z46,z7,z2,z196,z4]),(0,[z7,z15,z2,z194,z371]),(0,[z15,z420,z2,z21,z4])],[(0,[z110,z149,z3,z4,z5]),(0,[z15,z149,z3,z4,z324]),(0,[z59,z2,z84,z77,z13]),(0,[z37,z15,z3,z41,z24]),(0,[z7,z15,z2,z349,z866])],[(0,[z16,z1,z2,z21,z4]),(0,[z16,z15,z517,z4,z13]),(0,[z1482,z7,z2,z4,z13]),(0,[z15,z192,z193,z21,z4]),(0,[z7,z15,z2,z196,z276])],[(0,[z7,z81,z209,z4,z13]),(0,[z7,z48,z15,z4,z480]),(0,[z46,z37,z2,z4,z13]),(0,[z7,z15,z284,z214,z13]),(0,[z7,z15,z343,z4,z480])],[(0,[z7,z2,z114,z77,z314]),(0,[z16,z576,z2,z4,z78]),(0,[z46,z7,z2,z508,z9])]],
   [[(0,[z15,z2,z3,z1430,z4]),(0,[z7,z515,z3,z41,z9])],[(0,[z161,z7,z2,z331,z9]),(0,[z15,z149,z3,z4,z5]),(0,[z7,z2,z1483,z4,z13])],[(0,[z46,z304,z2,z4,z13]),(0,[z574,z2,z3,z21,z4])],[(0,[z16,z237,z2,z4,z13]),(0,[z91,z15,z2,z77,z42]),(0,[z7,z2,z3,z563,z35]),(0,[z54,z7,z345,z4,z13]),(0,[z46,z7,z2,z84,z9]),(0,[z46,z7,z2,z4,z212])],[(0,[z216,z237,z2,z4,z13]),(0,[z7,z159,z317,z4,z13])],[(0,[z882,z7,z2,z331,z13])],[(0,[z15,z2,z3,z4,z1484]),(0,[z37,z15,z77,z41,z13])],[(0,[z46,z7,z2,z4,z9]),(0,[z15,z2,z21,z1485,z4])]],
   [[(0,[z63,z2,z3,z4,z324]),(0,[z15,z97,z3,z21,z4]),(0,[z59,z2,z100,z84,z13]),(0,[z135,z2,z3,z21,z4]),(0,[z46,z7,z1486,z4,z13])],[(0,[z1253,z1,z2,z3,z4]),(0,[z46,z7,z2,z4,z341]),(0,[z7,z15,z2,z3,z1487]),(0,[z7,z412,z2,z331,z13])],[(0,[z15,z12,z372,z222,z13]),(0,[z10,z46,z12,z4,z13]),(0,[z37,z15,z3,z41,z9])],[(0,[z15,z2,z130,z4,z266]),(0,[z53,z2,z3,z21,z84])],[(0,[z7,z1,z2,z331,z9]),(0,[z1488,z15,z2,z21,z4])],[(0,[z63,z2,z3,z4,z5]),(0,[z1489,z7,z2,z4,z13]),(0,[z139,z2,z3,z21,z4]),(0,[z15,z2,z3,z50,z324]),(0,[z15,z27,z2,z156,z50]),(0,[z16,z59,z2,z32,z4]),(0,[z15,z2,z3,z1490,z4])],[(0,[z1007,z15,z12,z4,z13]),(0,[z7,z15,z2,z77,z314]),(0,[z15,z2,z21,z4,z284])],[(0,[z471,z1,z2,z4,z5]),(0,[z19,z7,z2,z4,z35]),(0,[z46,z133,z2,z32,z4])]],
   [[(0,[z15,z1264,z2,z4,z5]),(0,[z150,z517,z3,z4,z13]),(0,[z15,z2,z379,z21,z4]),(0,[z7,z59,z2,z331,z13]),(0,[z159,z2,z3,z21,z4])],[],[(0,[z16,z15,z149,z92,z13])],[(0,[z882,z16,z2,z4,z5]),(0,[z7,z15,z36,z331,z13]),(0,[z405,z15,z58,z21,z4]),(0,[z15,z2,z3,z1432,z4]),(0,[z46,z7,z2,z1491,z4])],[(0,[z7,z15,z3,z4,z1492]),(0,[z175,z15,z3,z21,z41])],[(0,[z7,z345,z3,z563,z13])],[(0,[z7,z15,z2,z1138,z9]),(0,[z7,z15,z317,z4,z9]),(0,[z7,z15,z27,z2,z336])],[(0,[z819,z7,z2,z4,z13]),(0,[z1493,z7,z2,z4,z13])]],
   [[(0,[z15,z2,z752,z21,z4]),(0,[z15,z27,z149,z92,z13]),(0,[z16,z264,z15,z2,z4]),(0,[z7,z15,z2,z1494,z4])],[(0,[z15,z149,z3,z4,z42]),(0,[z19,z49,z2,z50,z13]),(0,[z59,z2,z3,z331,z13]),(0,[z576,z15,z2,z3,z215]),(0,[z15,z2,z21,z4,z166]),(0,[z7,z308,z3,z4,z480])],[(0,[z15,z2,z1158,z21,z4])],[(0,[z1495,z7,z2,z4,z13]),(0,[z15,z149,z557,z4,z5]),(0,[z306,z2,z3,z4,z5]),(0,[z48,z15,z2,z797,z4])],[(0,[z185,z2,z3,z21,z4])],[(0,[z7,z15,z1082,z3,z9]),(0,[z7,z15,z345,z3,z314]),(0,[z7,z15,z3,z121,z480])],[(0,[z15,z1496,z3,z4,z13]),(0,[z63,z149,z3,z4,z5]),(0,[z46,z7,z2,z568,z13])],[(0,[z7,z15,z2,z538,z1231]),(0,[z7,z15,z2,z4,z1497]),(0,[z7,z15,z2,z1498,z4])]],
   [[],[(0,[z7,z15,z2,z4,z1499]),(0,[z2,z3,z21,z668,z4])],[(0,[z15,z517,z372,z4,z13]),(0,[z15,z2,z3,z74,z189]),(0,[z15,z2,z3,z21,z336]),(0,[z1005,z2,z3,z995,z4])],[(0,[z1097,z15,z2,z4,z5]),(0,[z53,z7,z2,z331,z119])],[(0,[z46,z2,z3,z21,z4])],[(0,[z15,z2,z3,z797,z4]),(0,[z15,z2,z3,z50,z1442]),(0,[z16,z720,z2,z21,z4]),(0,[z7,z15,z3,z4,z1500])],[(0,[z15,z2,z3,z4,z1501]),(0,[z15,z2,z587,z4,z88])],[(0,[z63,z2,z557,z4,z5]),(0,[z819,z7,z2,z4,z9]),(0,[z46,z7,z2,z4,z1502]),(0,[z15,z27,z2,z21,z77]),(0,[z1503,z2,z3,z21,z4])]],
   [[(0,[z46,z7,z2,z598,z4]),(0,[z16,z7,z15,z2,z1504])],[(0,[z15,z149,z4,z77,z5]),(0,[z15,z149,z300,z92,z13]),(0,[z7,z15,z2,z3,z1504]),(0,[z7,z2,z563,z88,z13]),(0,[z15,z418,z2,z587,z4]),(0,[z15,z2,z453,z21,z4])],[(0,[z48,z15,z149,z4,z5]),(0,[z59,z2,z4,z331,z13]),(0,[z46,z249,z2,z4,z13]),(0,[z7,z2,z267,z4,z13]),(0,[z48,z15,z2,z1505,z4]),(0,[z15,z2,z23,z21,z4]),(0,[z1506,z7,z2,z4,z13])],[(0,[z15,z517,z752,z4,z13]),(0,[z46,z7,z2,z4,z401]),(0,[z293,z2,z130,z4,z13]),(0,[z16,z2,z21,z995,z4])],[(0,[z37,z135,z3,z41,z13]),(0,[z1507,z15,z2,z3,z4])],[(0,[z139,z625,z2,z4,z13]),(0,[z15,z2,z74,z77,z13]),(0,[z1508,z7,z2,z4,z13]),(0,[z7,z15,z2,z4,z1509])],[(0,[z48,z15,z517,z4,z13]),(0,[z16,z2,z8,z21,z4])],[(0,[z15,z2,z3,z1510,z4]),(0,[z11,z12,z372,z4,z13]),(0,[z46,z7,z2,z4,z266]),(0,[z46,z49,z7,z2,z9]),(0,[z46,z582,z2,z4,z5]),(0,[z16,z59,z355,z4,z13]),(0,[z16,z25,z2,z4,z9])]],
   [[(0,[z16,z1,z2,z4,z389]),(0,[z15,z2,z797,z4,z77])],[(0,[z16,z59,z2,z4,z35]),(0,[z83,z7,z2,z331,z13]),(0,[z7,z15,z1511,z4,z13]),(0,[z7,z15,z2,z919,z9]),(0,[z7,z15,z453,z214,z13]),(0,[z7,z15,z2,z4,z1512]),(0,[z15,z2,z3,z4,z1513])],[(0,[z264,z15,z2,z3,z4]),(0,[z1183,z2,z3,z4,z5]),(0,[z16,z59,z2,z4,z865]),(0,[z7,z15,z23,z214,z13])],[(0,[z882,z16,z7,z2,z9]),(0,[z16,z15,z2,z74,z13]),(0,[z7,z15,z2,z276,z35])],[(0,[z46,z7,z210,z168,z13]),(0,[z46,z7,z2,z4,z246]),(0,[z7,z15,z2,z336,z419])],[(0,[z46,z7,z2,z28,z4]),(0,[z16,z48,z2,z21,z4]),(0,[z199,z7,z2,z4,z1262])],[(0,[z37,z15,z3,z214,z13]),(0,[z46,z7,z2,z32,z9]),(0,[z7,z15,z2,z4,z1514])],[(0,[z237,z2,z3,z4,z389]),(0,[z896,z15,z2,z92,z13]),(0,[z46,z7,z2,z331,z9])]],
   [[(0,[z15,z2,z3,z156,z218]),(0,[z7,z15,z4,z1515,z13]),(0,[z7,z15,z2,z336,z77])],[(0,[z1516,z7,z2,z222,z13]),(0,[z7,z2,z267,z4,z5]),(0,[z16,z7,z345,z132,z13]),(0,[z16,z7,z2,z1400,z4]),(0,[z7,z48,z15,z214,z13]),(0,[z15,z2,z123,z21,z4]),(0,[z7,z15,z2,z32,z276]),(0,[z46,z832,z2,z4,z13])],[(0,[z15,z2,z300,z74,z13]),(0,[z15,z2,z4,z1047,z5]),(0,[z264,z15,z2,z4,z77]),(0,[z46,z7,z2,z4,z356]),(0,[z7,z15,z2,z4,z1517])],[(0,[z150,z12,z3,z222,z13]),(0,[z46,z7,z149,z4,z13]),(0,[z53,z7,z2,z331,z9]),(0,[z16,z7,z345,z4,z101]),(0,[z1518,z15,z2,z3,z4]),(0,[z1519,z7,z2,z4,z13]),(0,[z7,z15,z2,z208,z336]),(0,[z473,z2,z3,z21,z4])],[(0,[z7,z2,z100,z563,z13]),(0,[z15,z2,z3,z1520,z4])],[(0,[z19,z7,z2,z4,z52]),(0,[z46,z7,z2,z254,z13])],[(0,[z1521,z7,z2,z4,z13]),(0,[z16,z59,z345,z4,z13]),(0,[z46,z7,z2,z1045,z4])],[(0,[z46,z7,z2,z244,z4]),(0,[z7,z8,z331,z41,z13]),(0,[z7,z15,z2,z462,z9]),(0,[z46,z7,z2,z1015,z13])]],
   [[(0,[z15,z2,z3,z21,z222]),(0,[z46,z7,z2,z466,z13]),(0,[z225,z7,z209,z3,z4]),(0,[z125,z15,z3,z41,z13]),(0,[z46,z2,z21,z4,z77])],[(0,[z1516,z7,z2,z4,z13]),(0,[z15,z2,z3,z1522,z4]),(0,[z16,z7,z345,z4,z13]),(0,[z1523,z15,z2,z3,z4]),(0,[z576,z2,z3,z4,z116])],[(0,[z11,z2,z3,z21,z4]),(0,[z15,z2,z130,z4,z383]),(0,[z91,z46,z7,z2,z9]),(0,[z46,z2,z4,z47,z5]),(0,[z7,z15,z2,z4,z309])],[(0,[z1,z2,z346,z4,z5]),(0,[z7,z15,z3,z214,z446]),(0,[z46,z7,z2,z168,z9])],[(0,[z15,z2,z3,z21,z143]),(0,[z302,z15,z2,z21,z4])],[],[(0,[z6,z264,z8,z3,z4]),(0,[z46,z576,z2,z4,z13]),(0,[z7,z15,z317,z32,z4]),(0,[z46,z7,z2,z215,z13]),(0,[z7,z15,z2,z4,z1524])],[(0,[z1,z2,z4,z331,z5]),(0,[z54,z1,z2,z4,z5]),(0,[z15,z149,z3,z92,z35]),(0,[z15,z2,z3,z211,z215])]],
   [[],[(0,[z46,z7,z2,z4,z439]),(0,[z59,z15,z2,z331,z13]),(0,[z1458,z15,z2,z3,z4])],[(0,[z16,z1,z2,z4,z183]),(0,[z15,z2,z4,z394,z5]),(0,[z16,z15,z2,z156,z50]),(0,[z48,z15,z2,z4,z520]),(0,[z1065,z2,z3,z4,z5])],[],[(0,[z15,z12,z3,z32,z222]),(0,[z7,z15,z2,z284,z314]),(0,[z46,z7,z2,z77,z314]),(0,[z15,z2,z3,z1525,z4]),(0,[z54,z59,z2,z4,z13]),(0,[z7,z44,z3,z214,z13]),(0,[z15,z2,z21,z1526,z4])],[(0,[z15,z2,z130,z4,z273]),(0,[z15,z2,z21,z4,z88])],[(0,[z46,z2,z50,z4,z5]),(0,[z374,z7,z2,z331,z13]),(0,[z16,z15,z2,z587,z4]),(0,[z308,z2,z3,z21,z4]),(0,[z1527,z7,z2,z4,z13]),(0,[z1360,z673,z2,z4,z13])],[(0,[z15,z2,z3,z1528,z4])]],
   [[(0,[z16,z7,z345,z4,z5])],[(0,[z15,z12,z3,z769,z13]),(0,[z46,z90,z2,z4,z5]),(0,[z1529,z7,z2,z4,z13])],[(0,[z908,z15,z2,z3,z5]),(0,[z63,z27,z2,z4,z5]),(0,[z15,z2,z21,z949,z4])],[(0,[z46,z673,z2,z4,z5])],[(0,[z15,z27,z2,z587,z4]),(0,[z1530,z7,z2,z4,z13]),(0,[z819,z7,z210,z168,z13]),(0,[z819,z7,z2,z4,z246]),(0,[z46,z15,z2,z21,z4])],[(0,[z15,z2,z510,z21,z4]),(0,[z15,z2,z3,z1531,z4])],[(0,[z15,z12,z752,z222,z13]),(0,[z15,z2,z130,z32,z4]),(0,[z7,z2,z3,z563,z101])],[(0,[z249,z2,z3,z563,z13])]],
   [[(0,[z15,z1082,z3,z4,z5]),(0,[z182,z15,z3,z41,z5]),(0,[z110,z149,z3,z92,z13]),(0,[z15,z2,z3,z74,z35]),(0,[z7,z15,z2,z351,z314]),(0,[z936,z15,z87,z4,z13]),(0,[z15,z2,z3,z1532,z4])],[(0,[z16,z63,z2,z4,z5]),(0,[z15,z2,z3,z4,z1533])],[(0,[z16,z1,z2,z4,z42]),(0,[z15,z2,z3,z74,z1534]),(0,[z7,z15,z3,z214,z35]),(0,[z16,z7,z707,z4,z13]),(0,[z7,z15,z2,z1535,z4])],[(0,[z15,z149,z3,z1100,z13]),(0,[z327,z2,z3,z21,z4])],[(0,[z7,z2,z3,z563,z13])],[(0,[z665,z7,z2,z331,z13]),(0,[z7,z15,z4,z77,z480])],[(0,[z1536,z7,z2,z4,z13]),(0,[z48,z15,z2,z21,z4]),(0,[z53,z249,z2,z331,z13]),(0,[z7,z241,z317,z4,z13]),(0,[z1537,z7,z15,z4,z13])],[(0,[z1538,z7,z2,z4,z13]),(0,[z67,z15,z2,z1015,z13]),(0,[z7,z44,z77,z41,z13])]],
   [[(0,[z15,z12,z3,z769,z5]),(0,[z15,z2,z3,z1539,z92]),(0,[z16,z7,z2,z563,z13])],[(0,[z7,z15,z3,z4,z1540]),(0,[z7,z345,z100,z84,z13]),(0,[z46,z1541,z2,z4,z13])],[(0,[z16,z1,z2,z156,z4]),(0,[z15,z2,z568,z3,z21]),(0,[z15,z2,z21,z1542,z4])],[(0,[z1,z2,z3,z4,z786]),(0,[z110,z2,z3,z21,z4]),(0,[z7,z48,z209,z4,z13]),(0,[z16,z7,z2,z744,z4]),(0,[z7,z44,z3,z41,z9]),(0,[z819,z7,z2,z168,z9])],[(0,[z48,z15,z2,z74,z13]),(0,[z46,z7,z2,z3,z314]),(0,[z7,z15,z2,z1543,z13]),(0,[z15,z345,z3,z21,z4]),(0,[z15,z2,z3,z21,z769])],[(0,[z15,z12,z3,z428,z222]),(0,[z15,z517,z3,z4,z35]),(0,[z91,z46,z2,z4,z5]),(0,[z264,z48,z15,z2,z4]),(0,[z7,z15,z2,z331,z218]),(0,[z1429,z7,z2,z121,z13])],[(0,[z16,z15,z12,z222,z13]),(0,[z46,z7,z2,z4,z383]),(0,[z15,z149,z3,z50,z5]),(0,[z7,z15,z2,z3,z1544]),(0,[z7,z345,z330,z4,z13]),(0,[z15,z2,z3,z1545,z4])],[(0,[z6,z8,z3,z21,z4]),(0,[z46,z7,z1546,z4,z13])]],
   [[(0,[z15,z2,z3,z21,z4]),(0,[z19,z7,z2,z4,z13]),(0,[z15,z2,z130,z4,z439]),(0,[z46,z7,z2,z4,z189]),(0,[z53,z7,z2,z32,z331]),(0,[z46,z1547,z2,z4,z13])],[(0,[z110,z2,z3,z74,z13]),(0,[z7,z15,z2,z331,z246]),(0,[z7,z15,z27,z214,z13]),(0,[z7,z15,z3,z32,z214])],[(0,[z63,z97,z3,z4,z5]),(0,[z7,z15,z2,z4,z1548]),(0,[z7,z15,z2,z331,z314]),(0,[z7,z15,z317,z4,z35]),(0,[z15,z2,z3,z797,z121]),(0,[z70,z46,z7,z4,z71]),(0,[z15,z2,z21,z506,z4])],[(0,[z15,z12,z3,z222,z1357]),(0,[z7,z2,z3,z563,z5]),(0,[z1549,z2,z3,z21,z4])],[(0,[z15,z27,z12,z222,z13]),(0,[z16,z7,z2,z4,z116]),(0,[z1057,z7,z15,z41,z13]),(0,[z7,z2,z3,z563,z9]),(0,[z46,z7,z2,z4,z1550])],[],[(0,[z16,z7,z755,z4,z13]),(0,[z15,z2,z3,z92,z1442]),(0,[z692,z15,z2,z331,z13]),(0,[z7,z15,z2,z3,z1551])],[(0,[z15,z2,z3,z156,z400]),(0,[z16,z7,z15,z2,z336]),(0,[z46,z1202,z2,z4,z13]),(0,[z46,z7,z2,z4,z790])]],
   [[(0,[z807,z2,z3,z4,z5]),(0,[z7,z15,z2,z3,z336])],[(0,[z46,z7,z2,z4,z273]),(0,[z7,z15,z27,z4,z480]),(0,[z15,z2,z4,z1552,z13])],[(0,[z7,z345,z3,z331,z13])],[(0,[z292,z15,z2,z21,z4]),(0,[z15,z517,z3,z222,z13]),(0,[z16,z86,z2,z21,z4]),(0,[z16,z59,z2,z4,z60]),(0,[z576,z308,z2,z3,z4]),(0,[z37,z15,z3,z41,z438]),(0,[z46,z186,z2,z4,z13]),(0,[z46,z7,z2,z4,z218])],[(0,[z7,z15,z2,z536,z9]),(0,[z7,z15,z2,z77,z939]),(0,[z15,z263,z2,z21,z4]),(0,[z264,z15,z81,z2,z4]),(0,[z7,z2,z3,z563,z55]),(0,[z46,z7,z2,z280,z13])],[(0,[z15,z2,z4,z460,z5]),(1,[z7,z345,z331,z13])],[(0,[z7,z2,z1553,z4,z13]),(0,[z818,z2,z3,z4,z5]),(0,[z46,z762,z2,z4,z5])],[(0,[z15,z2,z74,z351,z13]),(0,[z19,z7,z2,z4,z5]),(0,[z1183,z27,z2,z4,z5]),(0,[z15,z2,z3,z1505,z4]),(0,[z15,z2,z797,z4,z284])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 32 1024 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 1 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 1 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa1 : chunkB SA 2 ((parents.drop 8).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa2 : chunkB SA 2 ((parents.drop 16).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa3 : chunkB SA 2 ((parents.drop 23).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa4 : chunkB SA 2 ((parents.drop 30).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa5 : chunkB SA 2 ((parents.drop 38).take 9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa6 : chunkB SA 2 ((parents.drop 47).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa7 : chunkB SA 2 ((parents.drop 54).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa8 : chunkB SA 2 ((parents.drop 62).take 6) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 68)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [8, 8, 7, 7, 8, 9, 7, 8, 6] = true :=
  windowsG_cons pa0 (windowsG_cons pa1 (windowsG_cons pa2 (windowsG_cons pa3 (windowsG_cons pa4 (windowsG_cons pa5 (windowsG_cons pa6 (windowsG_cons pa7 (windowsG_cons pa8 (windowsG_nil paend)))))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 650) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 650).take 653) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1303).take 651) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1954).take 643) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb4 : chunkB SB 1 ((bkA.flatten.flatten.drop 2597).take 644) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb5 : chunkB SB 1 ((bkA.flatten.flatten.drop 3241).take 104) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 3345)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [650, 653, 651, 643, 644, 104] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_cons pb4 (windowsG_cons pb5 (windowsG_nil pbend))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 4 ((bkB.flatten.drop 0).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 4 ((bkB.flatten.drop 122).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 4 bkB.flatten 0 [122, 134] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 1) (J := 4) (d := 2) (g1 := 32) (nb1 := 1024) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36256

theorem PEqualNP.Outside.L_meta_36256 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276681440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276681440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36256.solve