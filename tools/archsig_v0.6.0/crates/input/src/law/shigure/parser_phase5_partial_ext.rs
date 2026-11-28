//! `shigure partial` の論理式・量子化階層・開領域構文解析（Phase 5 / AC2）。

use super::ast_phase5_obs::*;
use super::parser::PResult;
use crate::law::ast::{Ident, Span};
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::json::InputError;

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

impl<E: InputError> Parser<E> {
    fn peek_paren_is_formula(&self) -> bool {
        let mut depth = 0usize;
        let mut k = 0usize;
        while let Some(t) = self.peek_at(k) {
            if t.kind == TokenKind::Sym && t.text == "(" {
                depth += 1;
            } else if t.kind == TokenKind::Sym && t.text == ")" {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return false;
                }
            } else if depth == 1 {
                if t.kind == TokenKind::Sym && t.text == "=" {
                    return true;
                }
                if t.kind == TokenKind::Name
                    && matches!(
                        t.text.as_str(),
                        "and" | "or" | "not" | "exists" | "forall" | "defined" | "graph" | "rel"
                    )
                {
                    return true;
                }
            }
            k += 1;
        }
        false
    }

    fn parse_partial_term_args(&mut self) -> PResult<Vec<RawPartialTerm>, E> {
        self.expect_sym("(")?;
        let mut args = Vec::new();
        if !self.is_sym(")") {
            loop {
                self.checkpoint_here()?;
                args.push(self.parse_partial_term()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        Ok(args)
    }

    fn parse_partial_term(&mut self) -> PResult<RawPartialTerm, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            if self.eat_kw("let") {
                let start = self.prev_span().0;
                let var = self.ident()?;
                self.reject_forbidden_ident(&var, "partial formula let")?;
                self.expect_sym("=")?;
                let bound = self.parse_partial_term()?;
                self.expect_kw("in")?;
                let body = self.parse_partial_term()?;
                return Ok(RawPartialTerm::Let {
                    var,
                    bound: Box::new(bound),
                    body: Box::new(body),
                    span: (start, self.prev_end()),
                });
            }
            self.parse_partial_term_add()
        })
    }

    fn parse_partial_term_add(&mut self) -> PResult<RawPartialTerm, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let start = self.here().0;
            let mut lhs = self.parse_partial_term_mul()?;
            loop {
                self.checkpoint_here()?;
                if self.eat_sym("+") {
                    let rhs = self.parse_partial_term_mul()?;
                    lhs = RawPartialTerm::BinOp {
                        op: ShigurePartialArithOp::Add,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        span: (start, self.prev_end()),
                    };
                } else if self.eat_sym("-") {
                    let rhs = self.parse_partial_term_mul()?;
                    lhs = RawPartialTerm::BinOp {
                        op: ShigurePartialArithOp::Sub,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        span: (start, self.prev_end()),
                    };
                } else {
                    break;
                }
            }
            Ok(lhs)
        })
    }

    fn parse_partial_term_mul(&mut self) -> PResult<RawPartialTerm, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let start = self.here().0;
            let mut lhs = self.parse_partial_term_primary()?;
            while self.eat_sym("*") {
                self.checkpoint_here()?;
                let rhs = self.parse_partial_term_primary()?;
                lhs = RawPartialTerm::BinOp {
                    op: ShigurePartialArithOp::Mul,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: (start, self.prev_end()),
                };
            }
            Ok(lhs)
        })
    }

    fn parse_partial_term_primary(&mut self) -> PResult<RawPartialTerm, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            self.checkpoint_here()?;
            if self.eat_sym("(") {
                let inner = self.parse_partial_term()?;
                self.expect_sym(")")?;
                return Ok(inner);
            }
            if self.is_kw("slot") && self.peek_at(1).is_some_and(|t| t.text == "(") {
                self.advance();
                self.expect_sym("(")?;
                let s = self.ident()?;
                self.reject_forbidden_ident(&s, "partial term slot")?;
                self.expect_sym(")")?;
                return Ok(RawPartialTerm::Slot(s));
            }
            if self.is_kw("const") && self.peek_at(1).is_some_and(|t| t.text == "(") {
                self.advance();
                self.expect_sym("(")?;
                let (c, c_span) = self.parse_p5_symbol("partial term const")?;
                self.expect_sym(")")?;
                return Ok(RawPartialTerm::ExplicitConst(c, c_span));
            }
            if let Some(tok) = self.peek().cloned() {
                match tok.kind {
                    TokenKind::Str => {
                        let s = self.string()?;
                        return Ok(RawPartialTerm::ConstLit(s, tok.span));
                    }
                    TokenKind::Int => {
                        let n = self.expect_int_token()?;
                        return Ok(RawPartialTerm::ConstLit(n, tok.span));
                    }
                    TokenKind::Name => {
                        let start = tok.span.0;
                        let id = self.ident()?;
                        self.reject_forbidden_ident(&id, "partial term")?;
                        if self.is_sym("(") {
                            let args = self.parse_partial_term_args()?;
                            return Ok(RawPartialTerm::App {
                                op_name: id,
                                args,
                                span: (start, self.prev_end()),
                            });
                        }
                        return Ok(RawPartialTerm::IdentOrConst(id));
                    }
                    TokenKind::Sym => {}
                }
            }
            self.err("expected term in partial formula")
        })
    }

    fn parse_partial_formula(&mut self) -> PResult<RawPartialFormula, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || self.parse_partial_or())
    }

    fn parse_partial_or(&mut self) -> PResult<RawPartialFormula, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let start = self.here().0;
            let mut items = vec![self.parse_partial_and()?];
            while self.eat_kw("or") {
                self.checkpoint_here()?;
                items.push(self.parse_partial_and()?);
            }
            if items.len() == 1 {
                Ok(items.pop().unwrap())
            } else {
                Ok(RawPartialFormula::Or(items, (start, self.prev_end())))
            }
        })
    }

    fn parse_partial_and(&mut self) -> PResult<RawPartialFormula, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let start = self.here().0;
            let mut items = vec![self.parse_partial_unary()?];
            while self.eat_kw("and") {
                self.checkpoint_here()?;
                items.push(self.parse_partial_unary()?);
            }
            if items.len() == 1 {
                Ok(items.pop().unwrap())
            } else {
                Ok(RawPartialFormula::And(items, (start, self.prev_end())))
            }
        })
    }

    fn parse_partial_unary(&mut self) -> PResult<RawPartialFormula, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            self.checkpoint_here()?;
            if self.eat_kw("not") {
                let start = self.prev_span().0;
                let inner = self.parse_partial_unary()?;
                return Ok(RawPartialFormula::Not(
                    Box::new(inner),
                    (start, self.prev_end()),
                ));
            }
            let is_exists = self.eat_kw("exists");
            let is_forall = !is_exists && self.eat_kw("forall");
            if is_exists || is_forall {
                let start = self.prev_span().0;
                let var = self.ident()?;
                self.reject_forbidden_ident(&var, "partial quantifier")?;
                self.expect_sym(":")?;
                let sort = self.ident()?;
                self.reject_forbidden_ident(&sort, "partial quantifier sort")?;
                let restricted_domain = if self.eat_kw("in") {
                    Some(self.parse_p5_symbol_list("partial quantifier domain")?)
                } else {
                    None
                };
                self.expect_sym(".")?;
                let body = self.parse_partial_unary()?;
                let span = (start, self.prev_end());
                return Ok(if is_exists {
                    RawPartialFormula::Exists {
                        var,
                        sort,
                        restricted_domain,
                        body: Box::new(body),
                        span,
                    }
                } else {
                    RawPartialFormula::Forall {
                        var,
                        sort,
                        restricted_domain,
                        body: Box::new(body),
                        span,
                    }
                });
            }
            self.parse_partial_atom()
        })
    }

    fn parse_partial_atom(&mut self) -> PResult<RawPartialFormula, E> {
        if self.is_sym("(") && self.peek_paren_is_formula() {
            self.advance();
            let f = self.parse_partial_formula()?;
            self.expect_sym(")")?;
            return Ok(f);
        }
        if self.is_kw("defined") && self.peek_at(1).is_some_and(|t| t.text == "(") {
            let start = self.here().0;
            self.advance();
            self.expect_sym("(")?;
            let op_name = self.ident()?;
            self.reject_forbidden_ident(&op_name, "defined()")?;
            let args = self.parse_partial_term_args()?;
            self.expect_sym(")")?;
            return Ok(RawPartialFormula::Defined {
                op_name,
                args,
                span: (start, self.prev_end()),
            });
        }
        if self.is_kw("graph") && self.peek_at(1).is_some_and(|t| t.text == "(") {
            let start = self.here().0;
            self.advance();
            self.expect_sym("(")?;
            let op_name = self.ident()?;
            self.reject_forbidden_ident(&op_name, "graph()")?;
            let args = self.parse_partial_term_args()?;
            self.expect_sym(",")?;
            let output = self.parse_partial_term()?;
            self.expect_sym(")")?;
            return Ok(RawPartialFormula::Graph {
                op_name,
                args,
                output,
                span: (start, self.prev_end()),
            });
        }
        if self.is_kw("rel") && self.peek_at(1).is_some_and(|t| t.text == "(") {
            let start = self.here().0;
            self.advance();
            self.expect_sym("(")?;
            let rel_name = self.ident()?;
            self.reject_forbidden_ident(&rel_name, "rel()")?;
            let args = self.parse_partial_term_args()?;
            self.expect_sym(")")?;
            return Ok(RawPartialFormula::Rel {
                rel_name,
                args,
                span: (start, self.prev_end()),
            });
        }
        let start = self.here().0;
        let lhs = self.parse_partial_term()?;
        self.expect_sym("=")?;
        let rhs = self.parse_partial_term()?;
        Ok(RawPartialFormula::Eq(lhs, rhs, (start, self.prev_end())))
    }

    pub(super) fn parse_partial_eval_law(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawPartialEvalLaw, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("{")?;
        let mut is_required_law = None;
        let mut antecedent = None;
        let mut conclusion = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("required") {
                if is_required_law.is_some() {
                    return self.err("duplicate `required` clause in `eval_law`");
                }
                self.expect_sym("=")?;
                let flag = self.parse_shigure_bool("`eval_law` required")?;
                self.expect_sym(";")?;
                is_required_law = Some(flag);
            } else if self.eat_kw("antecedent") {
                if antecedent.is_some() {
                    return self.err("duplicate `antecedent` clause in `eval_law`");
                }
                self.expect_sym("=")?;
                antecedent = Some(self.parse_partial_formula()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("conclusion") {
                if conclusion.is_some() {
                    return self.err("duplicate `conclusion` clause in `eval_law`");
                }
                self.expect_sym("=")?;
                conclusion = Some(self.parse_partial_formula()?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(conclusion) = conclusion else {
            return self.p4_syntax_err(span, "`eval_law` requires a `conclusion` formula");
        };
        Ok(RawPartialEvalLaw {
            name,
            antecedent,
            conclusion,
            is_required_law: is_required_law.unwrap_or(true),
            span,
        })
    }

    pub(super) fn parse_quantifier_spec(&mut self, start: usize) -> PResult<RawQuantifierSpec, E> {
        let context = "`shigure partial` quantifier";
        self.expect_sym("{")?;
        let mut candidates: Option<Vec<Ident>> = None;
        let mut completions = Vec::new();
        let mut max_steps: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("candidates") {
                if candidates.is_some() {
                    return self.err("duplicate `candidates` clause in `quantifier`");
                }
                candidates = Some(self.parse_p4_ident_list(context)?);
                self.expect_sym(";")?;
            } else if self.eat_kw("completion") {
                let c_start = self.prev_span().0;
                let id = self.ident()?;
                self.reject_forbidden_ident(&id, context)?;
                self.expect_sym("{")?;
                let mut slot_values = Vec::new();
                let mut valid_candidates: Option<Vec<Ident>> = None;
                let mut output_value: Option<(String, Span)> = None;
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("slots") {
                        self.expect_sym("{")?;
                        while !self.is_sym("}") {
                            self.checkpoint_here()?;
                            let sv_start = self.here().0;
                            let slot = self.ident()?;
                            self.reject_forbidden_ident(&slot, context)?;
                            self.expect_sym("=")?;
                            let val = self.parse_p5_symbol(context)?;
                            self.expect_sym(";")?;
                            slot_values.push((slot, val, (sv_start, self.prev_end())));
                        }
                        self.expect_sym("}")?;
                    } else if self.eat_kw("valid") {
                        if valid_candidates.is_some() {
                            return self.err("duplicate `valid` clause in `completion`");
                        }
                        valid_candidates = Some(self.parse_p4_ident_list(context)?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("output") {
                        if output_value.is_some() {
                            return self.err("duplicate `output` clause in `completion`");
                        }
                        self.expect_sym("=")?;
                        output_value = Some(self.parse_p5_symbol(context)?);
                        self.expect_sym(";")?;
                    } else {
                        self.reject_conclusion_or_unknown(context)?;
                    }
                }
                self.expect_sym("}")?;
                let c_span = (c_start, self.prev_end());
                let Some(output_value) = output_value else {
                    return self.p4_syntax_err(c_span, "`completion` requires `output = ...;`");
                };
                completions.push(RawQuantifierCompletion {
                    id,
                    slot_values,
                    valid_candidates: valid_candidates.unwrap_or_default(),
                    output_value,
                    span: c_span,
                });
            } else if self.eat_kw("max_steps") {
                if max_steps.is_some() {
                    return self.err("duplicate `max_steps` clause in `quantifier`");
                }
                self.expect_sym("=")?;
                let n = self.parse_usize_token("`max_steps`")?;
                self.expect_sym(";")?;
                max_steps = Some(n);
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawQuantifierSpec {
            candidates: candidates.unwrap_or_default(),
            completions,
            max_steps,
            span: (start, self.prev_end()),
        })
    }

    fn parse_open_structure_side(&mut self, context: &str) -> PResult<RawOpenSide, E> {
        self.expect_sym("{")?;
        let mut sorts = Vec::new();
        let mut ops = Vec::new();
        let mut rels = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("sort") {
                let s_start = self.prev_span().0;
                let s_name = self.ident()?;
                self.reject_forbidden_ident(&s_name, context)?;
                self.expect_sym("=")?;
                let elems = self.parse_p5_symbol_list(context)?;
                self.expect_sym(";")?;
                sorts.push((s_name, elems, (s_start, self.prev_end())));
            } else if self.eat_kw("op_table") {
                let o_start = self.prev_span().0;
                let o_name = self.ident()?;
                self.reject_forbidden_ident(&o_name, context)?;
                self.expect_sym("(")?;
                let arg_sorts = self.parse_p4_ident_list(context)?;
                self.expect_sym(")")?;
                self.expect_sym("->")?;
                let out_sort = self.ident()?;
                self.reject_forbidden_ident(&out_sort, context)?;
                self.expect_sym("{")?;
                let mut entries = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    let e_start = self.here().0;
                    let args = self.parse_p5_symbol_list(context)?;
                    self.expect_sym("->")?;
                    let out = if self.eat_kw("none") {
                        None
                    } else {
                        Some(self.parse_p5_symbol(context)?)
                    };
                    self.expect_sym(";")?;
                    entries.push((args, out, (e_start, self.prev_end())));
                }
                self.expect_sym("}")?;
                ops.push(RawOpenOpTable {
                    name: o_name,
                    arg_sorts,
                    out_sort,
                    entries,
                    span: (o_start, self.prev_end()),
                });
            } else if self.eat_kw("rel_table") {
                let r_start = self.prev_span().0;
                let r_name = self.ident()?;
                self.reject_forbidden_ident(&r_name, context)?;
                self.expect_sym("(")?;
                let arg_sorts = self.parse_p4_ident_list(context)?;
                self.expect_sym(")")?;
                self.expect_sym("{")?;
                let mut entries = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    let e_start = self.here().0;
                    let args = self.parse_p5_symbol_list(context)?;
                    self.expect_sym(";")?;
                    entries.push((args, (e_start, self.prev_end())));
                }
                self.expect_sym("}")?;
                rels.push(RawOpenRelTable {
                    name: r_name,
                    arg_sorts,
                    entries,
                    span: (r_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawOpenSide { sorts, ops, rels })
    }

    pub(super) fn parse_open_domain(&mut self, start: usize) -> PResult<RawOpenDomain, E> {
        let context = "`shigure partial` open_domain";
        self.expect_sym("{")?;
        let mut sub_side: Option<RawOpenSide> = None;
        let mut amb_side: Option<RawOpenSide> = None;
        let mut fiber_checks = Vec::new();
        let mut positive_or_law = None;
        let mut affine_restriction = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("substructure") {
                if sub_side.is_some() {
                    return self.err("duplicate `substructure` block in `open_domain`");
                }
                sub_side = Some(self.parse_open_structure_side(context)?);
            } else if self.eat_kw("ambient") {
                if amb_side.is_some() {
                    return self.err("duplicate `ambient` block in `open_domain`");
                }
                amb_side = Some(self.parse_open_structure_side(context)?);
            } else if self.eat_kw("fiber_check") {
                let f_start = self.prev_span().0;
                let op_name = self.ident()?;
                self.reject_forbidden_ident(&op_name, context)?;
                self.expect_sym(":")?;
                let arg_sort = self.ident()?;
                self.reject_forbidden_ident(&arg_sort, context)?;
                self.expect_sym("->")?;
                let target_sort = self.ident()?;
                self.reject_forbidden_ident(&target_sort, context)?;
                self.expect_kw("targets")?;
                let known_targets = self.parse_p5_symbol_list(context)?;
                self.expect_sym(";")?;
                fiber_checks.push(RawFiberCoverageCheck {
                    op_name,
                    arg_sort,
                    target_sort,
                    known_targets,
                    span: (f_start, self.prev_end()),
                });
            } else if self.eat_kw("positive_law") {
                if positive_or_law.is_some() {
                    return self.err("duplicate `positive_law` block in `open_domain`");
                }
                positive_or_law = Some(self.parse_partial_eval_law(self.prev_span().0, context)?);
            } else if self.eat_kw("affine_restriction") {
                if affine_restriction.is_some() {
                    return self.err("duplicate `affine_restriction` block in `open_domain`");
                }
                let a_start = self.prev_span().0;
                self.expect_sym("{")?;
                let mut domain = None;
                let mut num_vars = None;
                let mut m_matrix = None;
                let mut b_rhs = None;
                let mut r_matrix = None;
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("domain") {
                        domain = Some(self.parse_shigure_coeff_domain()?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("num_vars") {
                        self.expect_sym("=")?;
                        num_vars = Some(self.parse_usize_token("`num_vars`")?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("m_matrix") {
                        self.expect_sym("=")?;
                        m_matrix = Some(self.parse_lit_matrix()?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("b_rhs") {
                        self.expect_sym("=")?;
                        b_rhs = Some(self.parse_shigure_lit_bracket_list()?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("r_matrix") {
                        self.expect_sym("=")?;
                        r_matrix = Some(self.parse_lit_matrix()?);
                        self.expect_sym(";")?;
                    } else {
                        self.reject_conclusion_or_unknown(context)?;
                    }
                }
                self.expect_sym("}")?;
                let a_span = (a_start, self.prev_end());
                let (Some(domain), Some(num_vars), Some(m_matrix), Some(b_rhs), Some(r_matrix)) =
                    (domain, num_vars, m_matrix, b_rhs, r_matrix)
                else {
                    return self.p4_syntax_err(
                        a_span,
                        "`affine_restriction` requires `domain`, `num_vars`, `m_matrix`, `b_rhs`, and `r_matrix`",
                    );
                };
                affine_restriction = Some(RawAffineRestriction {
                    domain,
                    m_matrix,
                    b_rhs,
                    r_matrix,
                    num_vars,
                    span: a_span,
                });
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(sub) = sub_side else {
            return self.p4_syntax_err(span, "`open_domain` requires `substructure` block");
        };
        let Some(amb) = amb_side else {
            return self.p4_syntax_err(span, "`open_domain` requires `ambient` block");
        };
        let Some(positive_or_law) = positive_or_law else {
            return self.p4_syntax_err(span, "`open_domain` requires `positive_law` block");
        };
        Ok(RawOpenDomain {
            substructure_sorts: sub.sorts,
            ambient_sorts: amb.sorts,
            substructure_ops: sub.ops,
            ambient_ops: amb.ops,
            substructure_rels: sub.rels,
            ambient_rels: amb.rels,
            fiber_checks,
            positive_or_law,
            affine_restriction,
            span,
        })
    }
}
