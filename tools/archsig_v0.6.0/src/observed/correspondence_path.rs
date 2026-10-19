//! 元correspondenceの対応表とfield対応から、同じU上の一段作用を作る。
use super::super::path_value::{PathValue, Step};
use super::internal_path::PathResult;
use super::*;
use crate::definition::model::PrimitiveSignature;
type Point = (String, String);
impl Environment<'_> {
    pub(super) fn correspondence_path(
        &self,
        id: usize,
        generator: &Scalar,
        signature: &PrimitiveSignature,
    ) -> Result<PathResult, ValidationFailure> {
        let PrimitiveSignature::Correspondence {
            from: ft,
            to: tt,
            maps,
            alignments,
            implicit,
            ..
        } = signature
        else {
            return Err("Pathの元宣言がcorrespondenceでない".into());
        };
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = generator
        else {
            return Err("correspondence生成元が原始参照でない".into());
        };
        let reading = self.path_reading(id)?;
        let original = self.subject(snapshot, subject)?;
        if original.ty != *entity {
            return Err("correspondenceの元型が違う".into());
        }
        let mut out = PathResult {
            value: None,
            scope: Scope::default(),
            support: vec![],
            missing: vec![],
            failure: None,
        };
        out.scope.readings.insert(reading.into());
        let from = self.path_slot(
            original,
            self.field(snapshot, subject, &format!("{entity}.from"))?,
            reading,
            &mut out,
        )?;
        let to = self.path_slot(
            original,
            self.field(snapshot, subject, &format!("{entity}.to"))?,
            reading,
            &mut out,
        )?;
        let (Some(from @ Scalar::Subject { .. }), Some(to @ Scalar::Subject { .. })) = (from, to)
        else {
            return Ok(out);
        };
        if from.ty() != Type::Ref(ft.clone()) || to.ty() != Type::Ref(tt.clone()) {
            return Err("correspondenceの実端点型が違う".into());
        }
        let point = |s: &Scalar| -> Result<Point, ValidationFailure> {
            if let Scalar::Subject {
                snapshot, subject, ..
            } = s
            {
                Ok((snapshot.clone(), subject.clone()))
            } else {
                Err("対応表の値が原始参照でない".into())
            }
        };
        let fp = point(&from)?;
        let tp = point(&to)?;
        // 検査済みMapの実rowを読み、結論や作用表を入力へ追加しない。
        let mut moving = BTreeMap::from([(fp.clone(), tp.clone())]);
        let mut by_type = BTreeMap::new();
        let mut unavailable = false;
        for (name, source_type, target_type) in maps {
            self.tick()?;
            by_type.insert(source_type.clone(), target_type.clone());
            let field = self.field(snapshot, subject, &format!("{entity}.{name}"))?;
            let Some(value) = self.path_slot(original, field, reading, &mut out)? else {
                unavailable = true;
                continue;
            };
            let Scalar::Map { pairs: entries, .. } = &value else {
                return Err("correspondenceの元対応表がMapでない".into());
            };
            for (a, b) in entries {
                self.tick()?;
                if a.ty() != Type::Ref(source_type.clone())
                    || b.ty() != Type::Ref(target_type.clone())
                {
                    return Err("correspondenceの対応表row型が違う".into());
                }
                if moving.insert(point(&a)?, point(&b)?).is_some() {
                    return Err("correspondenceの対応元が重複".into());
                }
            }
        }
        let mut fields = BTreeMap::new();
        for a in alignments {
            self.tick()?;
            fields.insert(a.source.clone(), a.target.clone());
        }
        for (a, b) in implicit {
            self.tick()?;
            fields.insert(a.clone(), b.clone());
        }
        // 共通Uとsourceの全owned族を、現在補完のownerも含めて決める。
        let mut universe = BTreeSet::new();
        let mut members = vec![];
        for snap in &self.inputs.archmap().snapshots {
            for s in &snap.subjects {
                self.tick()?;
                out.scope.merge(&self.scope(s, reading, None)?);
                universe.insert(Fact {
                    snapshot: s.snapshot.clone(),
                    subject: s.id.clone(),
                    field: None,
                    atom: None,
                });
                for f in &s.fields {
                    self.tick()?;
                    if let Slot::Known { atom, origin, .. } = &f.slot {
                        out.scope.merge(&self.scope(s, reading, Some(origin))?);
                        universe.insert(Fact {
                            snapshot: s.snapshot.clone(),
                            subject: s.id.clone(),
                            field: Some(f.name.clone()),
                            atom: Some(atom.clone()),
                        });
                    }
                }
                if (s.snapshot.as_str(), s.id.as_str()) == (fp.0.as_str(), fp.1.as_str()) {
                    members.push(s);
                } else if by_type.contains_key(&s.ty) {
                    let owner = self.path_slot(
                        s,
                        self.field(&s.snapshot, &s.id, &format!("{}.owner", s.ty))?,
                        reading,
                        &mut out,
                    )?;
                    match owner {
                        Some(owner) if point(&owner)? == fp => members.push(s),
                        Some(_) => {}
                        None => unavailable = true,
                    }
                }
            }
        }
        out.support.extend(universe.iter().cloned());
        if unavailable {
            out.support.sort();
            out.support.dedup();
            out.missing.sort();
            out.missing.dedup();
            return Ok(out);
        }
        let mut images = BTreeMap::new();
        let mut family = BTreeSet::new();
        for s in members {
            self.tick()?;
            let sp = (s.snapshot.clone(), s.id.clone());
            let target_point = moving
                .get(&sp)
                .ok_or("correspondenceの全域対応表に元subjectがない")?;
            let t = self.subject(&target_point.0, &target_point.1)?;
            let expected_type = if sp == fp {
                tt
            } else {
                by_type.get(&s.ty).ok_or("対応元の型がない")?
            };
            if &t.ty != expected_type {
                return Err("対応先の実subject型が違う".into());
            }
            let fact = Fact {
                snapshot: s.snapshot.clone(),
                subject: s.id.clone(),
                field: None,
                atom: None,
            };
            let image = Fact {
                snapshot: t.snapshot.clone(),
                subject: t.id.clone(),
                field: None,
                atom: None,
            };
            family.insert(fact.clone());
            images.insert(fact, image);
            for f in &s.fields {
                self.tick()?;
                let source_value = self.path_slot(s, f, reading, &mut out)?;
                if matches!(f.slot, Slot::Missing) {
                    continue;
                }
                let target_name = if sp == fp {
                    format!(
                        "{}.{}",
                        t.ty,
                        f.name.rsplit('.').next().ok_or("root field名がない")?
                    )
                } else {
                    fields
                        .get(&f.name)
                        .ok_or("検査済みfield対応がない")?
                        .clone()
                };
                let mut target_field = None;
                for f in &t.fields {
                    self.tick()?;
                    if f.name == target_name {
                        target_field = Some(f);
                        break;
                    }
                }
                let Some(target_field) = target_field else {
                    out.failure = Some((
                        Scalar::Text(format!("absent:{target_name}")),
                        Scalar::Text(format!("present:{target_name}")),
                    ));
                    continue;
                };
                let target_value = self.path_slot(t, target_field, reading, &mut out)?;
                let (Slot::Known { atom, .. }, Slot::Known { atom: ta, .. }) =
                    (&f.slot, &target_field.slot)
                else {
                    unavailable = true;
                    continue;
                };
                // Scalar補完を原始Atomに昇格しない。構造は元の既知Valueから読む。
                let (Slot::Known { value: a, .. }, Slot::Known { value: b, .. }) =
                    (&f.slot, &target_field.slot)
                else {
                    unreachable!()
                };
                let _ = (source_value, target_value);
                let mut refs = BTreeSet::new();
                let expected = self.path_shape(a, Some(&moving), &mut refs)?;
                let actual = self.path_shape(b, None, &mut BTreeSet::new())?;
                if !self.path_shape_same(&expected, &actual)? {
                    out.failure = Some((
                        Scalar::Text(self.path_shape_text(&actual)?),
                        Scalar::Text(self.path_shape_text(&expected)?),
                    ));
                }
                let fact = Fact {
                    snapshot: s.snapshot.clone(),
                    subject: s.id.clone(),
                    field: Some(f.name.clone()),
                    atom: Some(atom.clone()),
                };
                let image = Fact {
                    snapshot: t.snapshot.clone(),
                    subject: t.id.clone(),
                    field: Some(target_field.name.clone()),
                    atom: Some(ta.clone()),
                };
                family.insert(fact.clone());
                family.extend(refs);
                images.insert(fact, image);
            }
        }
        // source Fへ加わる外部参照の存在元は固定する。
        for fact in &family {
            self.tick()?;
            if fact.field.is_none() {
                images.entry(fact.clone()).or_insert_with(|| fact.clone());
            }
        }
        out.support.sort();
        out.support.dedup();
        out.missing.sort();
        out.missing.dedup();
        if unavailable || out.failure.is_some() {
            return Ok(out);
        }
        let target_root = Fact {
            snapshot: tp.0.clone(),
            subject: tp.1.clone(),
            field: None,
            atom: None,
        };
        let mut carrier = vec![];
        let mut action = vec![];
        for fact in universe {
            self.tick()?;
            let image = if family.contains(&fact) {
                images
                    .get(&fact)
                    .ok_or("correspondenceのF上像がない")?
                    .clone()
            } else {
                target_root.clone()
            };
            carrier.push(fact);
            action.push(image);
            #[cfg(test)]
            data::observe_actual(
                self.inputs.law().exprs[id].span,
                self.scoped_context
                    .get()
                    .or(self.context.get())
                    .unwrap_or_default(),
                "correspondence_action",
                carrier.len(),
            );
            self.tick()?;
        }
        let path = PathValue {
            reading: reading.into(),
            snapshot: fp.0,
            subject: fp.1,
            entity: ft.clone(),
            step: Some(Box::new(Step {
                generator: generator.clone(),
                word_tail: vec![],
                target: to,
                carrier,
                images: action,
            })),
        };
        path.check(&self.control)?;
        out.value = Some(Scalar::Path(Box::new(path)));
        self.tick()?;
        Ok(out)
    }
}
