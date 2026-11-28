//! 診断出力（パニック捕捉・ソース抜粋・類似候補サジェスト・SilenceReason 案内）の共通基盤。

use std::any::Any;
use std::backtrace::Backtrace;
use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::sync::Once;

/// 複数エラー一括収集の既定上限。
pub const DEFAULT_MAX_COLLECTED_ERRORS: usize = 50;

/// ソース抜粋の 1 行最大表示幅（Unicode scalar 数）。
const MAX_SNIPPET_LINE_WIDTH: usize = 160;

/// stderr へ出すバックトレース要約の最大行数。
const MAX_BACKTRACE_LINES: usize = 16;

/// stderr へ出すバックトレース要約の最大バイト数。
const MAX_BACKTRACE_BYTES: usize = 2048;

/// 捕捉したパニックの構造化情報。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PanicInfo {
    pub message: String,
    pub location: Option<String>,
    pub backtrace: Option<String>,
}

/// エラー箇所の 1 行ソース抜粋とキャレット表示。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceSnippet {
    pub line: usize,
    pub column: usize,
    pub source_line: String,
    pub caret_line: String,
}

thread_local! {
    static LAST_PANIC: RefCell<Option<PanicInfo>> = const { RefCell::new(None) };
    static VERBOSE_PANIC_BACKTRACE: Cell<bool> = const { Cell::new(false) };
}

static HOOK_ONCE: Once = Once::new();

struct VerboseGuard(bool);

impl Drop for VerboseGuard {
    fn drop(&mut self) {
        VERBOSE_PANIC_BACKTRACE.with(|cell| cell.set(self.0));
    }
}

/// `--verbose` 実行中のみパニックバックトレース要約を有効にする。
pub fn with_verbose_panic_backtrace<T>(enabled: bool, f: impl FnOnce() -> T) -> T {
    let prev = VERBOSE_PANIC_BACKTRACE.with(|cell| {
        let old = cell.get();
        cell.set(enabled);
        old
    });
    let _guard = VerboseGuard(prev);
    f()
}

/// `--verbose` または `RUST_BACKTRACE`（`0` 以外の非空値）が指定されているかを返す。
pub fn backtrace_requested() -> bool {
    if VERBOSE_PANIC_BACKTRACE.with(Cell::get) {
        return true;
    }
    std::env::var("RUST_BACKTRACE")
        .ok()
        .is_some_and(|v| !v.is_empty() && v != "0")
}

/// パニックのメッセージと発生位置をスレッドローカルへ記録するフックを登録する。
pub fn install_panic_hook() {
    HOOK_ONCE.call_once(|| {
        std::panic::set_hook(Box::new(|info| {
            let message = extract_payload_message(info.payload());
            let location = info
                .location()
                .map(|loc| format!("{}:{}", loc.file(), loc.line()));
            let backtrace = if backtrace_requested() {
                Some(summarize_backtrace(&Backtrace::force_capture()))
            } else {
                None
            };
            LAST_PANIC.with(|cell| {
                *cell.borrow_mut() = Some(PanicInfo {
                    message,
                    location,
                    backtrace,
                });
            });
        }));
    });
}

/// `catch_unwind` の `Err(payload)` から構造化パニック情報を取り出す。
pub fn capture_panic_from_unwind(payload: Box<dyn Any + Send>) -> PanicInfo {
    let payload_msg = extract_payload_message(&*payload);
    if let Some(mut recorded) = LAST_PANIC.with(|cell| cell.borrow_mut().take()) {
        if recorded.message.is_empty() {
            recorded.message = payload_msg;
        }
        return recorded;
    }
    PanicInfo {
        message: payload_msg,
        location: None,
        backtrace: if backtrace_requested() {
            Some(summarize_backtrace(&Backtrace::force_capture()))
        } else {
            None
        },
    }
}

/// 直近にフックが記録したスレッドローカルパニック情報をクリアする。
pub fn clear_last_panic() {
    LAST_PANIC.with(|cell| {
        *cell.borrow_mut() = None;
    });
}

/// バックトレースが記録されている場合、stderr 用の簡潔な要約を整形する。
pub fn format_panic_backtrace_stderr(info: &PanicInfo) -> Option<String> {
    let bt = info.backtrace.as_deref()?;
    let loc = info.location.as_deref().unwrap_or("unknown");
    Some(format!(
        "archsig internal panic: {} (at {loc})\nbacktrace summary:\n{bt}",
        info.message
    ))
}

fn extract_payload_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_owned()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "non-string panic payload".to_owned()
    }
}

fn summarize_backtrace(bt: &Backtrace) -> String {
    let raw = bt.to_string();
    let mut lines = Vec::new();
    let mut total_bytes = 0usize;
    let mut truncated = false;
    for line in raw.lines() {
        let trimmed = line.trim_end();
        if trimmed.is_empty() {
            continue;
        }
        if lines.len() >= MAX_BACKTRACE_LINES
            || total_bytes + trimmed.len() + 1 > MAX_BACKTRACE_BYTES
        {
            truncated = true;
            break;
        }
        total_bytes += trimmed.len() + 1;
        lines.push(trimmed);
    }
    if lines.is_empty() {
        "(backtrace unavailable)".to_owned()
    } else if truncated {
        format!("{}\n  ... (truncated)", lines.join("\n"))
    } else {
        lines.join("\n")
    }
}

/// 元入力バイト列と byte `span` から 1 行分のソース抜粋・行番号・列番号・キャレット行を生成する。
pub fn extract_source_snippet(bytes: &[u8], span: (usize, usize)) -> Option<SourceSnippet> {
    let text = std::str::from_utf8(bytes).unwrap_or_else(|e| {
        std::str::from_utf8(&bytes[..e.valid_up_to()]).expect("valid UTF-8 prefix")
    });
    let start = span.0;
    if start > text.len() || !text.is_char_boundary(start) {
        return None;
    }
    let end = span.1.clamp(start, text.len());
    let line_start = text[..start]
        .rfind('\n')
        .map_or(0, |pos| pos.saturating_add(1));
    let mut line_end = text[start..]
        .find('\n')
        .map_or(text.len(), |rel| start + rel);
    if line_end > line_start && text.as_bytes()[line_end - 1] == b'\r' {
        line_end -= 1;
    }
    let line = text[..start].bytes().filter(|&b| b == b'\n').count() + 1;
    let col_offset = text[line_start..start].chars().count();
    let column = col_offset + 1;
    let raw_line = &text[line_start..line_end];
    let span_end_in_line = end.min(line_end);
    let highlight_chars = if span_end_in_line > start && text.is_char_boundary(span_end_in_line) {
        text[start..span_end_in_line].chars().count().max(1)
    } else {
        1
    };

    let chars: Vec<char> = raw_line.chars().collect();
    if chars.len() <= MAX_SNIPPET_LINE_WIDTH {
        let mut caret_line = String::with_capacity(col_offset + highlight_chars);
        for &ch in chars.iter().take(col_offset) {
            caret_line.push(if ch == '\t' { '\t' } else { ' ' });
        }
        for _ in 0..highlight_chars {
            caret_line.push('^');
        }
        return Some(SourceSnippet {
            line,
            column,
            source_line: raw_line.to_owned(),
            caret_line,
        });
    }

    // 極端に長い行では該当列周辺だけを切り出し、キャレット位置を合わせる。
    let half = MAX_SNIPPET_LINE_WIDTH / 2;
    let win_start = col_offset.saturating_sub(half);
    let win_end = (win_start + MAX_SNIPPET_LINE_WIDTH).min(chars.len());
    let mut source_line = String::new();
    let mut prefix_len = 0usize;
    if win_start > 0 {
        source_line.push_str("...");
        prefix_len = 3;
    }
    for &ch in &chars[win_start..win_end] {
        source_line.push(ch);
    }
    if win_end < chars.len() {
        source_line.push_str("...");
    }
    let rel_col = col_offset.saturating_sub(win_start);
    let max_carets = chars.len().saturating_sub(col_offset).max(1);
    let visible_carets = highlight_chars
        .min(max_carets)
        .min(MAX_SNIPPET_LINE_WIDTH.saturating_sub(rel_col))
        .max(1);
    let mut caret_line = " ".repeat(prefix_len);
    for &ch in chars[win_start..].iter().take(rel_col) {
        caret_line.push(if ch == '\t' { '\t' } else { ' ' });
    }
    for _ in 0..visible_carets {
        caret_line.push('^');
    }
    Some(SourceSnippet {
        line,
        column,
        source_line,
        caret_line,
    })
}

/// Unicode scalar 単位の Levenshtein 編集距離を返す。
pub fn levenshtein(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    if a_chars.is_empty() {
        return b_chars.len();
    }
    if b_chars.is_empty() {
        return a_chars.len();
    }
    let mut prev: Vec<usize> = (0..=b_chars.len()).collect();
    let mut curr = vec![0usize; b_chars.len() + 1];
    for (i, &ca) in a_chars.iter().enumerate() {
        curr[0] = i + 1;
        for (j, &cb) in b_chars.iter().enumerate() {
            let cost = usize::from(ca != cb);
            curr[j + 1] = (prev[j + 1] + 1).min(curr[j] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[b_chars.len()]
}

/// 未定義識別子に対する類似候補を決定的にランキングして最大 `max_results` 件返す。
pub fn suggest_identifiers<'a>(
    target: &str,
    candidates: impl IntoIterator<Item = &'a str>,
    max_results: usize,
) -> Vec<String> {
    if target.is_empty() || max_results == 0 {
        return Vec::new();
    }
    let unique: BTreeSet<&str> = candidates
        .into_iter()
        .filter(|c| !c.is_empty() && *c != target)
        .collect();
    let target_lower = target.to_lowercase();
    let target_len = target.chars().count();
    let max_dist = match target_len {
        0..=2 => 1,
        3..=6 => 2,
        _ => (target_len / 3).min(3),
    };
    let target_split = target_lower.rsplit_once('.');

    let mut ranked: Vec<(usize, usize, &str)> = Vec::new();
    for cand in unique {
        let cand_lower = cand.to_lowercase();
        let full_dist = levenshtein(&target_lower, &cand_lower);
        let mut accepted = full_dist <= max_dist;
        let mut score = full_dist;

        if let (Some((tp, tl)), Some((cp, cl))) = (target_split, cand_lower.rsplit_once('.'))
            && tp == cp
        {
            let leaf_dist = levenshtein(tl, cl);
            let leaf_max = if tl.chars().count() <= 2 { 1 } else { 2 };
            if leaf_dist <= leaf_max {
                accepted = true;
                score = score.min(leaf_dist);
            }
        }
        if accepted {
            ranked.push((score, full_dist, cand));
        }
    }
    ranked.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)).then(a.2.cmp(b.2)));
    ranked
        .into_iter()
        .take(max_results)
        .map(|(_, _, cand)| cand.to_owned())
        .collect()
}

/// SHIGURE `SilenceReason` の推奨対処アクション（hint）を返す。
pub fn silence_reason_hint(reason_key: &str, limit_name: Option<&str>, slots: &[String]) -> String {
    match reason_key {
        "unobserved_dependency" => {
            if slots.is_empty() {
                "observe the missing coordinate slots in the ArchMap or run `archsig inspect` to list unobserved slots".to_owned()
            } else {
                let preview: Vec<&str> = slots.iter().take(3).map(String::as_str).collect();
                let suffix = if slots.len() > 3 {
                    format!(" (+{} more)", slots.len() - 3)
                } else {
                    String::new()
                };
                format!(
                    "record observations in ArchMap for missing slots [{}]{}; use `archsig inspect` to view slot types and owners",
                    preview.join(", "),
                    suffix
                )
            }
        }
        "resource_limit_exceeded" => {
            if let Some(name) = limit_name {
                format!(
                    "increase `--shigure-limit {name}=<value>` (run `archsig help` to list defaults) or split the presentation into smaller modules"
                )
            } else {
                "adjust `--shigure-limit <name>=<value>` or simplify/decompose the polynomial presentation".to_owned()
            }
        }
        "nonlinear_point_existence_out_of_scope" => {
            "existence checking over Q or Z with nonlinear constraints is undecidable/out of scope; linearize the constraints, add concrete bounds, or check over a finite field Fp(p)".to_owned()
        }
        "infinite_presentation_not_finitely_reducible" => {
            "ensure generators terminate under Gröbner reduction (add degree/bound hypotheses or factor the presentation into a finite quotient)".to_owned()
        }
        "unsupported_coeff_ring" => {
            "use a supported coefficient domain (`Q`, `Z`, or prime field `Fp(p)`) in the Law parameters".to_owned()
        }
        "quotient_ideal_out_of_scope" => {
            "simplify or bound the quotient ideal relations, or split nested quotient layers into separate tasks".to_owned()
        }
        "open_condition_in_interaction" => {
            "reformulate open inequality/non-equality guards as closed equations or finite-case checks for interaction analysis".to_owned()
        }
        "unbounded_search_out_of_scope" => {
            "bound free search variables or restrict the change family to finite candidate parameters".to_owned()
        }
        "constructible_stratification_out_of_scope" => {
            "reduce constructible stratification dimension or evaluate a restricted parameter slice".to_owned()
        }
        "finite_enumeration_out_of_scope" => {
            "reduce the finite domain cardinality, adjust enumeration limits via `--shigure-limit`, or fix additional slots in ArchMap".to_owned()
        }
        "universal_ring_out_of_scope" => {
            "specify an explicit concrete base ring (`Q`, `Z`, or `Fp(p)`) instead of a universal ring check".to_owned()
        }
        "non_noetherian_infinite_presentation" => {
            "replace infinitely generated assumptions with finitely presented ideal generators".to_owned()
        }
        "square_zero_condition_violated" => {
            "first-order lift requires square-zero deformation terms; remove higher-order products or verify deformation order".to_owned()
        }
        "syzygy_out_of_scope" => {
            "verify that input presentations lie over a supported commutative ring and reduce module generator count".to_owned()
        }
        "artin_order_out_of_scope" => {
            "reduce jet/Artin truncation order or verify linearity preconditions before running `shigure_artin`".to_owned()
        }
        "diagnostics_stratification_out_of_scope" => {
            "decompose the diagnostics system into lower-dimensional strata or fix invariant parameters".to_owned()
        }
        "disconnected_graph_out_of_scope" => {
            "connect isolated components in the diagram/path specification or analyze each connected component separately".to_owned()
        }
        "unsupported_completion_class" => {
            "use an affine/linear partial presentation class supported by completion reconstruction".to_owned()
        }
        "operator_not_uniquely_determined" => {
            "constrain the common operator part cleanly so `shigure_revision` can determine the before/after operator transition uniquely".to_owned()
        }
        "operator_revision_reuse_rejected" => {
            "re-run `archsig run` (or full `reobserve`) without cached SNF reuse when operators change across revisions".to_owned()
        }
        "applicability_condition_not_met" => {
            "inspect the failing applicability precondition in `applicability[]` (use `--detail full` or `archsig inspect --result`) and adjust the presentation to satisfy it".to_owned()
        }
        _ => "review input presentation, missing slots, or `--shigure-limit` bounds using `--detail full`".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extract_source_snippet_handles_ascii_multibyte_crlf_and_eof() {
        let src = "line one\r\n\"日本🦀\" bad\n";
        let pos = src.find("bad").unwrap();
        let snip = extract_source_snippet(src.as_bytes(), (pos, pos + 3)).unwrap();
        assert_eq!(snip.line, 2);
        assert_eq!(snip.column, 7);
        assert_eq!(snip.source_line, "\"日本🦀\" bad");
        assert_eq!(snip.caret_line, "      ^^^");

        // invalid UTF-8 suffix falls back to valid prefix cleanly
        let mut bad_utf8 = "\n日本🦀".as_bytes().to_vec();
        let start = bad_utf8.len();
        bad_utf8.push(0xff);
        let eof = extract_source_snippet(&bad_utf8, (start, start + 1)).unwrap();
        assert_eq!(eof.line, 2);
        assert_eq!(eof.column, 4);
        assert_eq!(eof.caret_line, "   ^");
    }

    #[test]
    fn suggest_identifiers_ranks_close_matches_and_avoids_distant_false_positives() {
        let cands = ["Counter.State", "Counter.Other", "Audit.State"];
        assert_eq!(
            suggest_identifiers("Counter.Stat", cands, 3),
            vec!["Counter.State".to_owned()]
        );
        // Existing test cli_validation_english uses "Counter.Missing": must stay empty
        assert!(suggest_identifiers("Counter.Missing", cands, 3).is_empty());

        assert_eq!(
            suggest_identifiers("amout", ["amount", "count", "bounded"], 3),
            vec!["amount".to_owned()]
        );
    }

    #[test]
    fn silence_reason_hint_covers_all_21_variants() {
        let keys = [
            "unobserved_dependency",
            "nonlinear_point_existence_out_of_scope",
            "infinite_presentation_not_finitely_reducible",
            "unsupported_coeff_ring",
            "quotient_ideal_out_of_scope",
            "open_condition_in_interaction",
            "unbounded_search_out_of_scope",
            "constructible_stratification_out_of_scope",
            "finite_enumeration_out_of_scope",
            "universal_ring_out_of_scope",
            "non_noetherian_infinite_presentation",
            "square_zero_condition_violated",
            "syzygy_out_of_scope",
            "artin_order_out_of_scope",
            "diagnostics_stratification_out_of_scope",
            "disconnected_graph_out_of_scope",
            "unsupported_completion_class",
            "operator_not_uniquely_determined",
            "operator_revision_reuse_rejected",
            "applicability_condition_not_met",
            "resource_limit_exceeded",
        ];
        for key in keys {
            let hint = silence_reason_hint(
                key,
                Some("max_groebner_s_pairs"),
                &["Counter.State.count".to_owned()],
            );
            assert!(!hint.is_empty(), "missing hint for {key}");
        }
    }

    #[test]
    fn panic_hook_captures_message_location_and_optional_backtrace() {
        install_panic_hook();
        clear_last_panic();
        let res = std::panic::catch_unwind(|| {
            panic!("boom diagnostics test");
        });
        let info = capture_panic_from_unwind(res.unwrap_err());
        assert_eq!(info.message, "boom diagnostics test");
        let loc = info.location.as_deref().expect("panic location");
        assert!(loc.contains("diagnostic.rs:"), "{loc}");

        let res_bt = with_verbose_panic_backtrace(true, || {
            std::panic::catch_unwind(|| {
                panic!("boom verbose");
            })
        });
        let info_bt = capture_panic_from_unwind(res_bt.unwrap_err());
        assert!(info_bt.backtrace.is_some());
        let formatted = format_panic_backtrace_stderr(&info_bt).unwrap();
        assert!(formatted.contains("boom verbose"));
        assert!(formatted.contains("backtrace summary:"));
    }
}
