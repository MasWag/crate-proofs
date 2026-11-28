use leb128fmt::Error;

pub fn source_is_none(error: &Error) -> bool {
    matches!(<Error as std::error::Error>::source(error), None)
}

#[allow(deprecated)]
pub fn cause_is_none(error: &Error) -> bool {
    matches!(<Error as std::error::Error>::cause(error), None)
}
