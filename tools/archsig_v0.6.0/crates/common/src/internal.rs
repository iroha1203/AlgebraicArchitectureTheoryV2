//! 内部エラーの本文と発生位置。位置は公開wireの本文に混ぜない。
use std::{borrow::Cow, fmt, panic::Location};

#[derive(Clone)]
pub struct InternalError {
    message: Cow<'static, str>,
    location: &'static Location<'static>,
}
impl InternalError {
    #[doc(hidden)]
    #[track_caller]
    pub fn new(message: Cow<'static, str>) -> Self {
        Self {
            message,
            location: Location::caller(),
        }
    }
    pub fn message(&self) -> &str {
        &self.message
    }
    pub fn location(&self) -> &'static Location<'static> {
        self.location
    }
    pub fn into_message(self) -> String {
        self.message.into_owned()
    }
}
impl fmt::Display for InternalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.message.fmt(f)
    }
}
impl fmt::Debug for InternalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.message, f)
    }
}
impl PartialEq for InternalError {
    fn eq(&self, other: &Self) -> bool {
        self.message == other.message
    }
}
impl Eq for InternalError {}
impl std::error::Error for InternalError {}

/// 内部エラーを発生位置とともに作る。固定文面は割当てず保持する。
/// 可変値を含む文面は `format!(...)` または書式と追加引数で渡す。
#[macro_export]
macro_rules! internal {
    ($message:literal) => {
        $crate::internal::InternalError::new(::std::borrow::Cow::Borrowed($message))
    };
    ($message:expr) => {
        $crate::internal::InternalError::new(::std::borrow::Cow::Owned(::std::convert::Into::<String>::into($message)))
    };
    ($format:literal, $($args:tt)+) => {
        $crate::internal::InternalError::new(::std::borrow::Cow::Owned(format!($format, $($args)+)))
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn location_is_the_creation_site_and_does_not_change_message_or_equality() {
        let line = line!() + 1;
        let error = crate::internal!("internal failure");
        assert_eq!(error.location().file(), file!());
        assert_eq!(error.location().line(), line);
        assert!(matches!(error.message, std::borrow::Cow::Borrowed(_)));
        let other = crate::internal!("internal {}", "failure");
        assert_ne!(error.location().line(), other.location().line());
        assert_eq!(error, other);
        let label = "internal";
        let formatted = crate::internal!(format!("{label} failure"));
        assert_eq!(formatted, error);
        #[track_caller]
        fn forwarded() -> super::InternalError {
            crate::internal!("internal failure")
        }
        let forwarded_line = line!() + 1;
        let forwarded = forwarded();
        assert_eq!(forwarded.location().line(), forwarded_line);
        assert_eq!(forwarded, error);
        assert_eq!(error.to_string(), "internal failure");
        assert_eq!(format!("{error:?}"), "\"internal failure\"");
        assert_eq!(error.into_message(), "internal failure");
        assert_eq!(other.into_message(), "internal failure");
    }
}
