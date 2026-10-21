//! 参照を含まない数値型の恒等写像を、有限標本を使わず型の全域に構成する。
use super::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
    numeric,
    result::{Scalar, ValidationFailure},
    value_transport::{DeclarationValuePosition, selected_types},
};
use crate::{
    archmap::Value,
    canonical::Json,
    construction::{
        ConstructionFailure,
        maps::{ConfigurationOperation, DeclarationCorrespondence},
    },
    types::Type,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericTransportValue {
    value: Scalar,
}
impl NumericTransportValue {
    pub fn ty(&self) -> Type {
        self.value.ty()
    }
    pub fn wire(&self) -> Json {
        self.value.wire()
    }
}

/// Z/Q/Fpの各元を固定し、Tupleの位置を保つ写像 x ↦ x。
/// 型は対応済み宣言から選ぶ。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericValueMap {
    ty: Type,
}
impl NumericValueMap {
    pub fn ty(&self) -> &Type {
        &self.ty
    }
    pub fn apply(
        &self,
        value: &Value,
        control: &mut Control,
    ) -> Result<NumericTransportValue, ConstructionFailure> {
        tick(control)?;
        let value = numeric::from_input(value, &self.ty, control)
            .map_err(invalid_value)?
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent("数値写像の型が数値型でない".into())
            })?;
        tick(control)?;
        Ok(NumericTransportValue { value })
    }
    pub fn apply_value(
        &self,
        value: &NumericTransportValue,
        control: &mut Control,
    ) -> Result<NumericTransportValue, ConstructionFailure> {
        self.apply_scalar(&value.value, control)
    }
    pub(super) fn apply_scalar(
        &self,
        value: &Scalar,
        control: &mut Control,
    ) -> Result<NumericTransportValue, ConstructionFailure> {
        tick(control)?;
        if value.ty() != self.ty {
            return Err(ConstructionFailure::InvalidSelection(
                "数値写像の引数型が違う".into(),
            ));
        }
        numeric::check(value, control).map_err(invalid_value)?;
        let value = NumericTransportValue {
            value: value.clone(),
        };
        tick(control)?;
        Ok(value)
    }
}
impl NumericTransportValue {
    pub(super) fn scalar(&self) -> &Scalar {
        &self.value
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericValueTransport {
    declarations: DeclarationCorrespondence,
    declaration: String,
    position: DeclarationValuePosition,
    forward: NumericValueMap,
    inverse: NumericValueMap,
}
impl NumericValueTransport {
    pub fn operation(&self) -> &ConfigurationOperation {
        self.declarations.operation()
    }
    pub fn declaration(&self) -> &str {
        &self.declaration
    }
    pub fn position(&self) -> DeclarationValuePosition {
        self.position
    }
    pub fn source_type(&self) -> &Type {
        self.forward.ty()
    }
    pub fn target_type(&self) -> &Type {
        self.inverse.ty()
    }
    pub fn forward(&self) -> &NumericValueMap {
        &self.forward
    }
    pub fn inverse(&self) -> &NumericValueMap {
        &self.inverse
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        tick(control)?;
        if self
            != &numeric_declaration_value_transport(
                inputs,
                &self.declarations,
                &self.declaration,
                self.position,
                control,
            )?
        {
            return Err(ConstructionFailure::Inconsistent(
                "数値型の全域対応が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::NumericValueTransport)
        .map_err(Into::into)
}
fn invalid_value(failure: ValidationFailure) -> ConstructionFailure {
    match failure {
        ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
        failure => ConstructionFailure::InvalidSelection(format!(
            "数値型または正規値の条件を満たさない: {failure:?}"
        )),
    }
}

/// 対応済み宣言の同一数値型で順逆とも恒等写像を生成する。
/// 原始数値は固定、有限積は同じ各位置の恒等の積なので、両合成は全域で恒等である。
/// 数値以外はこのnative APIの適用域外であり、公開問いの算法判定ではない。
pub fn numeric_declaration_value_transport(
    inputs: &CheckedInputs,
    declarations: &DeclarationCorrespondence,
    declaration: &str,
    position: DeclarationValuePosition,
    control: &mut Control,
) -> Result<NumericValueTransport, ConstructionFailure> {
    tick(control)?;
    declarations.recheck(inputs, control)?;
    let (source, target) = selected_types(declarations, declaration, position, control)?;
    // 既存核はZ/Q/Fpとその有限Tuple積を再帰的に判定する。全域を列挙しない。
    if !numeric::is_numeric_type(&source, control).map_err(invalid_value)?
        || !numeric::is_numeric_type(&target, control).map_err(invalid_value)?
    {
        return Err(ConstructionFailure::InvalidSelection(
            "数値値域APIの適用域でない型".into(),
        ));
    }
    if source != target {
        return Err(ConstructionFailure::Inconsistent(
            "対応済みの数値型が一致しない".into(),
        ));
    }
    let result = NumericValueTransport {
        declarations: declarations.clone(),
        declaration: declaration.into(),
        position,
        forward: NumericValueMap { ty: source },
        inverse: NumericValueMap { ty: target },
    };
    tick(control)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        construction::maps::{correspondence, declaration_correspondence},
        observed::input::{InputSources, check_inputs},
    };
    fn example() -> (CheckedInputs, NumericValueTransport) {
        let left = include_bytes!("../../tests/fixtures/configuration-map-left.atoms.json");
        let right = include_bytes!("../../tests/fixtures/configuration-map-right.atoms.json");
        let defs =
            crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &defs.vocabularies["Left"].digest;
        let rd = &defs.vocabularies["Right"].digest;
        let bridge = include_str!("../../tests/fixtures/configuration-map-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd);
        let defs = crate::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let expand = |s: &str| {
            s.replace("@LEFT_DIGEST@", ld)
                .replace("@RIGHT_DIGEST@", rd)
                .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
                .into_bytes()
        };
        let inputs = check_inputs(
            InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                expand(include_str!(
                    "../../tests/fixtures/numeric-value-transport.law"
                )),
                expand(include_str!(
                    "../../tests/fixtures/reference-type.archmap.json"
                )),
            ),
            &mut Control::unlimited(),
        )
        .unwrap();
        let c = correspondence(
            &inputs,
            "v",
            "m",
            "Before",
            Some("After"),
            &mut Control::unlimited(),
        )
        .unwrap();
        let d = declaration_correspondence(&inputs, c.map().unwrap(), &mut Control::unlimited())
            .unwrap();
        let r = numeric_declaration_value_transport(
            &inputs,
            &d,
            "Before.axes",
            DeclarationValuePosition::Parameter(1),
            &mut Control::unlimited(),
        )
        .unwrap();
        (inputs, r)
    }
    #[test]
    fn recheck_rejects_forged_source_target_and_declaration_positions() {
        let (inputs, r) = example();
        let mut variants = Vec::new();
        let mut m = r.clone();
        m.forward.ty = Type::Q;
        variants.push(m);
        let mut m = r.clone();
        m.inverse.ty = Type::Q;
        variants.push(m);
        let mut m = r.clone();
        m.forward.ty = Type::Q;
        m.inverse.ty = Type::Q;
        variants.push(m);
        let mut m = r.clone();
        m.forward.ty = Type::Bool;
        variants.push(m);
        let mut m = r.clone();
        m.declaration = "Before.returned".into();
        variants.push(m);
        let mut m = r.clone();
        m.position = DeclarationValuePosition::Parameter(2);
        variants.push(m);
        let mut m = r.clone();
        m.position = DeclarationValuePosition::Return;
        variants.push(m);
        for m in &variants {
            assert!(
                m.recheck(&inputs, &mut Control::unlimited()).is_err(),
                "{m:?}"
            );
        }
        assert_eq!(variants.len(), 7);
        r.recheck(&inputs, &mut Control::unlimited()).unwrap();
    }
    #[test]
    fn numeric_kernel_rejects_forged_noncanonical_typed_values() {
        let (inputs, r) = example();
        let q = numeric_declaration_value_transport(
            &inputs,
            &r.declarations,
            "Before.axes",
            DeclarationValuePosition::Parameter(2),
            &mut Control::unlimited(),
        )
        .unwrap();
        for value in [
            Scalar::Q(2.into(), 4.into()),
            Scalar::Q(1.into(), 0.into()),
            Scalar::Q(1.into(), (-1).into()),
        ] {
            assert!(matches!(
                q.inverse
                    .apply_value(&NumericTransportValue { value }, &mut Control::unlimited()),
                Err(ConstructionFailure::InvalidSelection(_))
            ));
        }
    }
}
