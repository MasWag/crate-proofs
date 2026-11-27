pub fn decode_error_source<'a>(e: &'a utf8::DecodeError<'a>) -> Option<&'a (dyn std::error::Error + 'static)> {
    std::error::Error::source(e)
}

pub fn decode_error_source_is_none(e: &utf8::DecodeError<'_>) -> bool {
    std::error::Error::source(e).is_none()
}
