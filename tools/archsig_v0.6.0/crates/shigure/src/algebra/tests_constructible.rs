use crate::algebra::constructible::{ConstructibleSet, LocallyClosedStratum};
use crate::algebra::constructible_image::{project_constructible_set, project_stratum_image};
use crate::algebra::poly::{Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::ir::result::SilenceReason;

fn vars(names: &[&str]) -> VarOrder {
    VarOrder::new(names.iter().map(|s| (*s).to_owned()).collect()).expect("valid var order")
}

fn r(n: i64) -> Rat {
    Rat::from_int(n)
}

#[test]
fn constructible_boolean_algebra_laws_and_membership() {
    let v = vars(&["x", "y"]);
    let x = Poly::var(2, 0, Rat::zero());
    let y = Poly::var(2, 1, Rat::zero());
    let one = Poly::one(2, Rat::zero());

    // A = V(x) ∪ D(x * y - 1)
    let a = ConstructibleSet::closed(v.clone(), vec![x.clone()])
        .unwrap()
        .union(&ConstructibleSet::open(v.clone(), vec![x.mul(&y).sub(&one)]).unwrap())
        .unwrap();
    // B = D(y)
    let b = ConstructibleSet::open(v.clone(), vec![y.clone()]).unwrap();
    // C = V(y - 1)
    let c = ConstructibleSet::closed(v.clone(), vec![y.sub(&one)]).unwrap();

    // Commutativity and associativity
    assert!(a.union(&b).unwrap().equals(&b.union(&a).unwrap()).unwrap());
    assert!(
        a.intersect(&b)
            .unwrap()
            .equals(&b.intersect(&a).unwrap())
            .unwrap()
    );
    assert!(
        a.union(&b)
            .unwrap()
            .union(&c)
            .unwrap()
            .equals(&a.union(&b.union(&c).unwrap()).unwrap())
            .unwrap()
    );
    assert!(
        a.intersect(&b)
            .unwrap()
            .intersect(&c)
            .unwrap()
            .equals(&a.intersect(&b.intersect(&c).unwrap()).unwrap())
            .unwrap()
    );

    // Distributivity
    let dist_lhs = a.intersect(&b.union(&c).unwrap()).unwrap();
    let dist_rhs = a
        .intersect(&b)
        .unwrap()
        .union(&a.intersect(&c).unwrap())
        .unwrap();
    assert!(dist_lhs.equals(&dist_rhs).unwrap());

    // Double complement & De Morgan
    let a_comp = a.complement().unwrap();
    assert!(a_comp.complement().unwrap().equals(&a).unwrap());
    assert!(a.intersect(&a_comp).unwrap().is_empty());
    assert!(
        a.union(&a_comp)
            .unwrap()
            .equals(&ConstructibleSet::whole_space(v.clone()))
            .unwrap()
    );

    let dm_lhs = a.union(&b).unwrap().complement().unwrap();
    let dm_rhs = a_comp.intersect(&b.complement().unwrap()).unwrap();
    assert!(dm_lhs.equals(&dm_rhs).unwrap());

    // Difference identity: A \ B == A ∩ B^c
    assert!(
        a.difference(&b)
            .unwrap()
            .equals(&a.intersect(&b.complement().unwrap()).unwrap())
            .unwrap()
    );

    // Point membership checks
    assert!(a.contains_point(&[r(0), r(0)]).unwrap()); // on V(x)
    assert!(!a.contains_point(&[r(1), r(1)]).unwrap()); // x != 0 and x*y - 1 == 0
    assert!(a_comp.contains_point(&[r(1), r(1)]).unwrap());
    assert!(a.contains_point(&[r(2), r(1)]).unwrap()); // x*y - 1 == 1 != 0
}

#[test]
fn d6_projection_xy_equals_one_returns_open_dx_not_closure_a1() {
    // Fiber var y first, param var x second: [y, x]
    let total = vars(&["y", "x"]);
    let param = vars(&["x"]);
    let y = Poly::var(2, 0, Rat::zero());
    let x = Poly::var(2, 1, Rat::zero());
    let one = Poly::one(2, Rat::zero());

    let hyperbola = ConstructibleSet::closed(total, vec![x.mul(&y).sub(&one)]).unwrap();
    let image = project_constructible_set(&hyperbola, 1, &param).unwrap();

    let px = Poly::var(1, 0, Rat::zero());
    let expected_dx = ConstructibleSet::open(param.clone(), vec![px]).unwrap();
    let closure_a1 = ConstructibleSet::whole_space(param);

    assert!(image.equals(&expected_dx).unwrap());
    assert!(!image.equals(&closure_a1).unwrap());
    assert!(!image.contains_point(&[r(0)]).unwrap());
    assert!(image.contains_point(&[r(1)]).unwrap());
    assert!(image.contains_point(&[r(-3)]).unwrap());
}

#[test]
fn d6_projection_handles_fiber_open_condition_and_w5_gm_cover() {
    // Test 1: (x - 2)*(y - 1) = 0 with D(y - 1) projects onto V(x - 2).
    let param = vars(&["x"]);
    let y = Poly::var(2, 0, Rat::zero());
    let x = Poly::var(2, 1, Rat::zero());
    let one = Poly::one(2, Rat::zero());
    let two = Poly::constant(2, r(2));
    let stratum = LocallyClosedStratum {
        equations: vec![x.sub(&two).mul(&y.sub(&one))],
        invertibles: vec![y.sub(&one)],
    };
    let img = project_stratum_image(&stratum, 1, &param).unwrap();
    let px = Poly::var(1, 0, Rat::zero());
    let p_two = Poly::constant(1, r(2));
    let expected = ConstructibleSet::closed(param.clone(), vec![px.sub(&p_two)]).unwrap();
    assert!(img.equals(&expected).unwrap());
    assert!(img.contains_point(&[r(2)]).unwrap());
    assert!(!img.contains_point(&[r(3)]).unwrap());

    // Test 2: W5 z^2 = t on G_{m,t} x G_{m,z} projects to D(t) (= G_{m,t}).
    let w5_total = vars(&["z", "t"]);
    let z = Poly::var(2, 0, Rat::zero());
    let t = Poly::var(2, 1, Rat::zero());
    let w5_set =
        ConstructibleSet::locally_closed(w5_total, vec![z.pow(2).sub(&t)], vec![z, t]).unwrap();
    let t_param = vars(&["t"]);
    let w5_img = project_constructible_set(&w5_set, 1, &t_param).unwrap();
    let pt = Poly::var(1, 0, Rat::zero());
    let expected_gm = ConstructibleSet::open(t_param, vec![pt]).unwrap();
    assert!(w5_img.equals(&expected_gm).unwrap());
}

#[test]
fn d6_projection_handles_non_reduced_base_and_zero_dim_param_space() {
    // Non-reduced base: (rho - 1)^2 = 0, fiber: (rho - 1)*z + z - 1 = 0 -> at geometric point rho = 1, z = 1 non-empty!
    let total = vars(&["z", "rho"]);
    let param = vars(&["rho"]);
    let z = Poly::var(2, 0, Rat::zero());
    let rho = Poly::var(2, 1, Rat::zero());
    let one = Poly::one(2, Rat::zero());
    let rho_m1 = rho.sub(&one);
    let set =
        ConstructibleSet::closed(total, vec![rho_m1.pow(2), rho_m1.mul(&z).add(&z).sub(&one)])
            .unwrap();
    let img = project_constructible_set(&set, 1, &param).unwrap();
    assert!(img.contains_point(&[r(1)]).unwrap());
    assert!(!img.contains_point(&[r(2)]).unwrap());

    // Zero-dimensional param space (Spec Q): [y] -> []
    let y_only = vars(&["y"]);
    let empty_param = vars(&[]);
    let y = Poly::var(1, 0, Rat::zero());
    let nonempty_pt = ConstructibleSet::closed(
        y_only.clone(),
        vec![y.pow(2).add(&Poly::one(1, Rat::zero()))],
    )
    .unwrap();
    let pt_img = project_constructible_set(&nonempty_pt, 1, &empty_param).unwrap();
    assert!(!pt_img.is_empty());
    assert!(pt_img.contains_point(&[]).unwrap());

    let empty_fiber = ConstructibleSet::locally_closed(y_only, vec![y.clone()], vec![y]).unwrap();
    assert!(empty_fiber.is_empty());
    let empty_img = project_constructible_set(&empty_fiber, 1, &empty_param).unwrap();
    assert!(empty_img.is_empty());
}

#[test]
fn constructible_branch_limit_triggers_silence_not_false_result() {
    // 7 independent parameter variables c0..c6 with c_i * y^(i+1) = 0 produce a full binary
    // closed/open split tree of 2^7 = 128 non-empty branches, exceeding DEFAULT_MAX_IMAGE_BRANCHES (64).
    let total = vars(&["y", "c0", "c1", "c2", "c3", "c4", "c5", "c6"]);
    let param = vars(&["c0", "c1", "c2", "c3", "c4", "c5", "c6"]);
    let y = Poly::var(8, 0, Rat::zero());

    let mut eqs = Vec::new();
    for i in 0..7 {
        let c_i = Poly::var(8, i + 1, Rat::zero());
        eqs.push(c_i.mul(&y.pow((i + 1) as u32)));
    }
    let stratum = LocallyClosedStratum {
        equations: eqs,
        invertibles: vec![],
    };
    let _ = total;
    let res = project_stratum_image(&stratum, 1, &param);
    assert!(matches!(
        res,
        Err(SilenceReason::ConstructibleStratificationOutOfScope { .. })
    ));
}

#[test]
fn constructible_y_pair_limit_error_bounds_empty_whole_and_spoly_vanish_branch() {
    // 1. DEFAULT_MAX_IMAGE_Y_PAIRS (256) limit: 25 generators vanishing at (0, 0) (hence fiber never
    // collapses to 1 = 0) and sharing y1*y2 in every leading monomial generate > 256 S-pairs with
    // zero branch splits.
    let y_vars = vars(&["y1", "y2"]);
    let empty_param = vars(&[]);
    let y1 = Poly::var(2, 0, Rat::zero());
    let y2 = Poly::var(2, 1, Rat::zero());
    let tail = y1.checked_mul(&y2).unwrap();
    let mut many_gens = Vec::new();
    for k in 1..=25u32 {
        many_gens.push(y1.pow(26 - k).checked_mul(&y2.pow(k)).unwrap().add(&tail));
    }
    let ypair_res = project_stratum_image(
        &LocallyClosedStratum {
            equations: many_gens,
            invertibles: vec![],
        },
        2,
        &empty_param,
    );
    let _ = y_vars;
    assert!(matches!(
        ypair_res,
        Err(SilenceReason::ConstructibleStratificationOutOfScope { .. })
    ));

    // 2. Variable order mismatch and point dimension mismatch errors.
    let v_xy = vars(&["x", "y"]);
    let v_xz = vars(&["x", "z"]);
    let c_xy = ConstructibleSet::empty(v_xy.clone());
    let c_xz = ConstructibleSet::empty(v_xz);
    assert!(c_xy.union(&c_xz).is_err());
    assert!(c_xy.intersect(&c_xz).is_err());
    assert!(c_xy.difference(&c_xz).is_err());
    assert!(c_xy.is_subset_of(&c_xz).is_err());
    assert!(c_xy.equals(&c_xz).is_err());
    assert!(c_xy.contains_point(&[r(1)]).is_err());

    // 3. empty().complement() == whole_space() and whole_space().complement().is_empty().
    let whole = ConstructibleSet::whole_space(v_xy.clone());
    assert!(c_xy.complement().unwrap().equals(&whole).unwrap());
    assert!(whole.complement().unwrap().is_empty());

    // 4. S-polynomial leading coefficient that can vanish and be nonzero when new_lm != 1:
    // fiber [y1, y2], param [c], equations {y1*y2 - 1, y1^2 - c*y2}.
    // S-poly gives -c*y2^2 + y1 (new_lm = y2^2 != 1, new_lc = -c).
    // Branch c = 0 fails (y1 = 0 conflicts with y1*y2 = 1); branch D(c) succeeds -> image is D(c).
    let fvars = vars(&["y1", "y2", "c"]);
    let cparam = vars(&["c"]);
    let fy1 = Poly::var(3, 0, Rat::zero());
    let fy2 = Poly::var(3, 1, Rat::zero());
    let fc = Poly::var(3, 2, Rat::zero());
    let fone = Poly::one(3, Rat::zero());
    let fset = ConstructibleSet::closed(
        fvars,
        vec![fy1.mul(&fy2).sub(&fone), fy1.pow(2).sub(&fc.mul(&fy2))],
    )
    .unwrap();
    let fimg = project_constructible_set(&fset, 2, &cparam).unwrap();
    let expected_dc = ConstructibleSet::open(cparam, vec![Poly::var(1, 0, Rat::zero())]).unwrap();
    assert!(fimg.equals(&expected_dc).unwrap());
    assert!(!fimg.contains_point(&[r(0)]).unwrap());
    assert!(fimg.contains_point(&[r(1)]).unwrap());
}
