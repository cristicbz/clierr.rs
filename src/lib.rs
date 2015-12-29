//! A small library which provides convenient, non-panicking error handling for small CLI scripts.
#![deny(missing_docs)]
#![deny(unused)]

use std::borrow::Cow;
use std::env;
use std::error::Error as StdError;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::io::{self, Write};
use std::path::Path;
use std::process;

/// A minimalist error type to use in CLI scripts: it wraps an arbitrary cause which implements
/// `std::error::Error` and a description for the `Display` implementation.
#[derive(Debug)]
pub struct Error {
    description: Option<Cow<'static, str>>,
    cause: Option<Box<StdError>>,
}

impl Error {
    /// Creates a new `Error` with a description and a cause.
    ///
    /// In most cases you'll want to use the convenient `DescribeErr` trait or the `ctry`
    /// and `ccheck` macros.
    ///
    /// With a `&'static str`:
    ///
    /// ```
    ///    # use clierr::Error;
    ///    # let some_error = Error::with_description("x");
    /// Error::new("oh no!", some_error);
    /// ```
    ///
    /// With a `String`:
    ///
    /// ```
    ///    # use clierr::Error;
    ///    # let some_error = Error::with_description("x");
    ///    # let filename = "file.txt";
    /// Error::new(format!("should not have tried to open '{}'!", filename), some_error);
    /// ```
    pub fn new<S, E>(description: S, cause: E) -> Error
        where S: Into<Cow<'static, str>>,
              E: StdError + 'static
    {
        Error {
            description: Some(description.into()),
            cause: Some(Box::new(cause)),
        }
    }

    /// Creates a new error with a descrption but no cause. Useful for validation specific
    /// errors where there's no underlying error (e.g. CLI timeout argument must be
    /// greater than zero).
    pub fn with_description<S: Into<Cow<'static, str>>>(description: S) -> Error {
        Error {
            description: Some(description.into()),
            cause: None,
        }
    }

    /// Creates a new error with a cause, but no description. The `Display` implementation
    /// forwards to that of `cause` in this case.
    ///
    /// In most cases you'll want to use the convenient `DescribeErr` trait or the `ctry`
    /// and `ccheck` macros instead.
    pub fn caused_by<E: StdError + 'static>(cause: E) -> Error {
        Error {
            description: None,
            cause: Some(Box::new(cause)),
        }
    }
}

/// A trait which enables adding a description to any `Result` by wrapping its error type in an
/// `Error`
///
/// An implementation is provided for `Result<S, E: std::errror::Error` and it's not really meant to
/// be implemented for anything else (unless you're using some kind of custom `Result` type).
pub trait DescribeErr: Sized {
    /// The result of describing the `Result`'s error.
    type Described;

    /// Wraps the error contained by `Self` in an `Error` with the given description.
    fn describe_err<D>(self, description: D) -> Self::Described where D: Into<Cow<'static, str>>;

    /// Same as `describe_err`, but defer the construction of the description until it's actually
    /// needed (i.e. only in the error case for a `Result`).
    fn describe_err_with<F, D>(self, with: F) -> Self::Described
        where F: FnOnce() -> D,
              D: Into<Cow<'static, str>>;
}

impl<S, E: StdError + 'static> DescribeErr for Result<S, E> {
    type Described = Result<S, Error>;

    fn describe_err<D: Into<Cow<'static, str>>>(self, description: D) -> Result<S, Error> {
        self.map_err(|cause| Error::new(description, cause))
    }

    fn describe_err_with<F, D>(self, with: F) -> Result<S, Error>
        where F: FnOnce() -> D,
              D: Into<Cow<'static, str>>
    {
        self.map_err(|cause| Error::new(with(), cause))
    }
}

impl Display for Error {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        if let Some(description) = self.description.as_ref() {
            write!(fmt, "{}", description)
        } else if let Some(cause) = self.cause() {
            write!(fmt, "{}", cause)
        } else {
            write!(fmt, "<unknown error>")
        }
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        if let Some(description) = self.description.as_ref() {
            description
        } else if let Some(cause) = self.cause() {
            cause.description()
        } else {
            ""
        }
    }

    fn cause(&self) -> Option<&StdError> {
        self.cause.as_ref().map(|e| &**e)
    }
}

const MAX_CAUSE_RECURSION: usize = 32;

fn print_cause(prefix: &str, error: &StdError, max_recursion: usize) {
    if max_recursion == 0 {
        // We've recursed too many times; don't want to overflow so bail here. Ignore any errors.
        let _ = writeln!(io::stderr(), "{}:    ...", prefix);
    } else if let Some(cause) = error.cause() {
        // Display the current cause, and recurse if (a) the current cause is caused by another
        // error and (b) the write to stderr didn't fail the first time.
        if writeln!(io::stderr(), "{}:    caused by: {}", prefix, cause).is_err() {
            return;
        }

        // Hopefully tail recursive, but not a big deal if not.
        print_cause(prefix, cause, max_recursion - 1);
    }
}

fn run_impl<E, F>(main: F) -> i32
    where F: FnOnce() -> Result<(), E>,
          E: Into<Box<StdError>>
{
    if let Err(error) = main() {
        let error = error.into();
        let argv0 = env::args().next();
        let program_name = argv0.as_ref()
                                .and_then(|s| Path::new(s).file_name())
                                .map(|os| os.to_string_lossy());
        let prefix = program_name.as_ref().map(|s| &**s).unwrap_or("<unknown>");

        if writeln!(io::stderr(), "{}: {}", prefix, error).is_ok() {
            print_cause(prefix, &*error, MAX_CAUSE_RECURSION);
        }
        1
    } else {
        0
    }
}

/// Runs a `Result`-returning function and exits the process with 0 if successful.
///
/// If `main` returns an error, it displays it (and all its causes recursively) to `stderr` and
/// exists the process with 1.
pub fn run_and_exit<E, F>(main: F) -> !
    where F: FnOnce() -> Result<(), E>,
          E: Into<Box<StdError>>
{
    process::exit(run_impl(main))
}

/// Like `try!`, but in the error case the error is wrapped in an `Error` with a given description
/// (which can be specified using `format_args!` syntax).
///
/// Example:
///
/// ```norust
///     ctry!(File::open(filename), "could not open output file {}", filename)
/// ```
///
/// Note: If you don't like macros, the `DescribeErr` trait already cuts on a lot of verbosity.
#[macro_export]
macro_rules! ctry {
    ($e:expr, $fmt:expr) => {{
        use $crate::DescribeErr;
        try!($e.describe_err_with(|| $fmt))
    }};
    ($e:expr, $fmt:expr, $($arg:tt)*) => {{
        use $crate::DescribeErr;
        try!($e.describe_err_with(|| format!($fmt, $($arg)*)))
    }}
}

/// Like `assert!` but instead of panicking it early-returns an `Error` with a given description
/// (which can be specified using `format_args!` syntax).
///
/// Example:
///
/// ```norust
///     ccheck!(value(key) == 42, "value of {} was not 42 ({})", key, value(key))
/// ```
///
/// Note: If you don't like macros, the `DescribeErr` trait already cuts on a lot of verbosity.
#[macro_export]
macro_rules! ccheck {
    ($e:expr, $fmt:expr) => {{
        use $crate::Error;
        if !($e) {
            return Err(Error::with_description($fmt)).into();
        }
    }};
    ($e:expr, $fmt:expr, $($arg:tt)*) => {{
        use $crate::Error;
        if !($e) {
            return Err(Error::with_description(format!($fmt, $($arg)*))).into();
        }
    }}
}

#[cfg(test)]
mod test {
    use super::{Error, DescribeErr, run_impl};
    use std::error::Error as StdError;
    use std::cell::Cell;

    fn ok() -> Result<(), Error> {
        Ok(())
    }

    fn err() -> Result<(), Error> {
        Err(Error::with_description("test"))
    }

    fn err_box() -> Result<(), Box<StdError>> {
        Err(Box::new(Error::with_description("test")))
    }

    #[test]
    fn error() {
        let with_static = Error::new("test", Error::with_description("cause"));
        let with_owned = Error::new("test2".to_owned(),
                                    Error::caused_by(Error::with_description("cause2")));

        assert_eq!(&format!("{}", with_static), "test");
        assert_eq!(&format!("{}", with_owned), "test2");
        assert_eq!(with_static.description(), "test");
        assert_eq!(with_owned.description(), "test2");

        assert_eq!(with_static.cause().map(|c| c.description()), Some("cause"));
        assert!(with_static.cause().unwrap().cause().is_none());

        assert_eq!(with_owned.cause().map(|c| c.description()), Some("cause2"));
        assert!(with_owned.cause().unwrap().cause().unwrap().cause().is_none());
        assert_eq!(with_owned.cause().map(|c| format!("{}", c)),
                   Some("cause2".to_owned()));
        assert_eq!(with_owned.cause().and_then(|c| c.cause()).map(|c| c.description()),
                   Some("cause2"));
    }

    #[test]
    fn describe_err() {
        let counter = Cell::new(0);
        let inc = || {
            counter.set(counter.get() + 1);
            "wrapper"
        };

        assert!(ok().describe_err("wrapper").is_ok());
        assert!(ok().describe_err_with(&inc).is_ok());
        assert_eq!(counter.get(), 0);

        let described = err().describe_err("wrapper");
        match described {
            Err(error) => {
                assert_eq!(error.description(), "wrapper");
                assert_eq!(error.cause().map(|c| c.description()), Some("test"));
            }
            Ok(()) => panic!("failed: {:?}", described),
        }

        let described = err().describe_err_with(&inc);
        assert_eq!(counter.get(), 1);
        match described {
            Err(error) => {
                assert_eq!(error.description(), "wrapper");
                assert_eq!(error.cause().map(|c| c.description()), Some("test"));
            }
            Ok(()) => panic!("failed: {:?}", described),
        }
    }

    #[test]
    fn ctry_ok() {
        fn foo() -> Result<u32, Error> {
            let _ = ctry!(ok(), "oh no!");
            Ok(42)
        }
        assert_eq!(foo().unwrap(), 42);
    }

    #[test]
    fn ctry_err() {
        fn foo() -> Result<u32, Error> {
            let _ = ctry!(err(), "help {}", "us");
            Ok(42)
        }
        match foo() {
            Err(e) => {
                assert_eq!(e.description(), "help us");
                assert_eq!(e.cause().unwrap().description(), "test");
            }
            Ok(x) => panic!("failed: {:?}", x),
        }
    }

    #[test]
    fn ccheck_ok() {
        fn foo() -> Result<u32, Error> {
            ccheck!(true, "oh no!");
            Ok(42)
        }
        assert_eq!(foo().unwrap(), 42);
    }

    #[test]
    fn ccheck_err() {
        fn foo() -> Result<u32, Error> {
            ccheck!(false, "help {}", "us");
            Ok(42)
        }
        match foo() {
            Err(e) => {
                assert_eq!(e.description(), "help us");
                assert!(e.cause().is_none());
            }
            Ok(x) => panic!("failed: {:?}", x),
        }
    }

    #[test]
    fn run_returns_zero_for_success() {
        assert_eq!(run_impl(ok), 0);
    }

    #[test]
    fn run_returns_one_for_error() {
        assert_eq!(run_impl(err), 1);
    }

    #[test]
    fn run_returns_one_for_error_box() {
        assert_eq!(run_impl(err_box), 1);
    }
}
