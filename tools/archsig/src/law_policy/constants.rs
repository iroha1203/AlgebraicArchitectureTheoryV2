pub(super) const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "law policy is selected analysis policy, not AAT itself",
    "law policy validation does not prove architecture lawfulness",
    "law policy validation does not certify atom truth",
    "missing coverage is not measured zero",
    "signature zero requires ArchSig analysis with declared coverage and exactness assumptions",
];

pub(super) const REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS: [&str; 4] = [
    "spectrum measurement profile is a measurement recipe, not a law universe",
    "profile differences are not law universe differences",
    "unmeasured axes are not zero",
    "spectrum zero requires coverage, exactness, and zero-reflection assumptions",
];

pub(super) const REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS: [&str; 5] = [
    "homotopy measurement profile is a measurement recipe, not a law universe",
    "candidate paths and loops are review cues, not path truth",
    "unfilled loops are architectural holes, not automatic violations",
    "missing filler evidence is not measured zero",
    "nonzero holonomy does not prove future incidents or repair unsafety",
];

pub(super) const REQUIRED_PART4_DISTANCE_PROFILE_NON_CONCLUSIONS: [&str; 4] = [
    "part4 distance profile is a selected measurement recipe, not a law universe",
    "profile weights and costs are read from LawPolicy, not inferred from schema shape",
    "unmeasured distance is not measured zero",
    "operation distance requires a declared profile cost or explicit calibration evidence",
];

pub(super) const MAX_PART4_DISTANCE_PROFILE_WEIGHT: i64 = 1_000_000;
pub(super) const MAX_PART4_OPERATION_COST: i64 = 1_000_000;
