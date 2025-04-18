extern crate proc_macro;
use proc_macro::{
    Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream,
    TokenTree,
};
use quote::quote;

struct Error {
    message: String,
    span: Span,
}

impl Error {
    fn into_compile_error(self) -> TokenStream {
        TokenStream::from_iter(vec![
            TokenTree::Ident(Ident::new("compile_error", self.span)),
            TokenTree::Punct({
                let mut punct = Punct::new('!', Spacing::Alone);
                punct.set_span(self.span);
                punct
            }),
            TokenTree::Group({
                let mut group = Group::new(Delimiter::Brace, {
                    TokenStream::from_iter(vec![TokenTree::Literal({
                        let mut string = Literal::string(&self.message);
                        string.set_span(self.span);
                        string
                    })])
                });
                group.set_span(self.span);
                group
            }),
        ])
    }
}

/// lit!(width, value) construct a BitSet with a specified width from a literal
/// value.
#[proc_macro]
pub fn bitset(input: TokenStream) -> TokenStream {
    match bitset_impl(input) {
        Ok(out) => out,
        Err(e) => e.into_compile_error(),
    }
}

fn bitset_impl(input: TokenStream) -> Result<TokenStream, Error> {
    let mut iter = input.into_iter();
    let nxt = iter.next().ok_or_else(|| Error {
        message: "expected width literal".to_owned(),
        span: Span::call_site(),
    })?;

    let width_tok = match nxt {
        TokenTree::Literal(l) => Ok(l),
        unexpected => Err(Error {
            message: "only literal numbers are supported for width".to_owned(),
            span: unexpected.span(),
        }),
    }?;
    let width_str = width_tok.to_string();
    let width: usize = match width_str.parse() {
        Ok(n) => Ok(n),
        Err(_) => Err(Error {
            message: "unable to parse as number".to_owned(),
            span: width_tok.span(),
        }),
    }?;

    let nxt = iter.next().ok_or_else(|| Error {
        message: "expected comma".to_owned(),
        span: Span::call_site(),
    })?;

    let comma = match nxt {
        TokenTree::Punct(p) => Ok(p),
        unexpected => Err(Error {
            message: "expected comma literal".to_owned(),
            span: unexpected.span(),
        }),
    }?;

    if comma.to_string() != "," {
        return Err(Error {
            message: "expected comma".to_owned(),
            span: comma.span(),
        });
    }

    let nxt = iter.next().ok_or_else(|| Error {
        message: "expected value as integer literal".to_owned(),
        span: Span::call_site(),
    })?;

    let lit = match nxt {
        TokenTree::Literal(l) => Ok(l),
        unexpected => Err(Error {
            message: "only literal numbers are supported for value".to_owned(),
            span: unexpected.span(),
        }),
    }?;

    let lit_str = lit.to_string().replace("_", "");

    let number = match lit_str.strip_prefix("0x") {
        Some(stripped) => u128::from_str_radix(stripped, 16),
        None => match lit_str.strip_prefix("0b") {
            Some(stripped) => u128::from_str_radix(stripped, 2),
            None => lit_str.parse::<u128>(),
        },
    }
    .map_err(|_| Error {
        message: "unable to parse as number".to_owned(),
        span: lit.span(),
    })?;

    let actual_width = 128 - number.leading_zeros() as usize;
    if actual_width > width {
        return Err(Error {
            message: "literal value is greater than specified width".to_owned(),
            span: Span::call_site(),
        });
    }

    let tokens = match width {
        w if w <= 8 => {
            let a = number as u8;
            quote! {
                BitSet::<#width>([#a])
            }
        }
        w if w <= 16 => {
            let [a, b] = (number as u16).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b])
            }
        }
        w if w <= 24 => {
            let [a, b, c, _] = (number as u32).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c])
            }
        }
        w if w <= 32 => {
            let [a, b, c, d] = (number as u32).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d])
            }
        }
        w if w <= 40 => {
            let [a, b, c, d, e, _, _, _] = (number as u64).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e])
            }
        }
        w if w <= 48 => {
            let [a, b, c, d, e, f, _, _] = (number as u64).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f])
            }
        }
        w if w <= 56 => {
            let [a, b, c, d, e, f, g, _] = (number as u64).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f, #g])
            }
        }
        w if w <= 64 => {
            let [a, b, c, d, e, f, g, h] = (number as u64).to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f, #g, #h])
            }
        }
        w if w <= 72 => {
            let [a, b, c, d, e, f, g, h, i, _, _, _, _, _, _, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f, #g, #h, #i])
            }
        }
        w if w <= 80 => {
            let [a, b, c, d, e, f, g, h, i, j, _, _, _, _, _, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f, #g, #h, #i, #j])
            }
        }
        w if w <= 88 => {
            let [a, b, c, d, e, f, g, h, i, j, k, _, _, _, _, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f, #g, #h, #i, #j, #k])
            }
        }
        w if w <= 96 => {
            let [a, b, c, d, e, f, g, h, i, j, k, l, _, _, _, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([#a, #b, #c, #d, #e, #f, #g, #h, #i, #j, #k, #l])
            }
        }
        w if w <= 104 => {
            let [a, b, c, d, e, f, g, h, i, j, k, l, m, _, _, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([
                    #a, #b, #c, #d, #e, #f, #g, #h,
                    #i, #j, #k, #l, #m
                ])
            }
        }
        w if w <= 112 => {
            let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, _, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([
                    #a, #b, #c, #d, #e, #f, #g, #h,
                    #i, #j, #k, #l, #m, #n
                ])
            }
        }
        w if w <= 120 => {
            let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, _] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([
                    #a, #b, #c, #d, #e, #f, #g, #h,
                    #i, #j, #k, #l, #m, #n, #o
                ])
            }
        }
        _ => {
            let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] =
                number.to_le_bytes();
            quote! {
                BitSet::<#width>([
                    #a, #b, #c, #d, #e, #f, #g, #h,
                    #i, #j, #k, #l, #m, #n, #o, #p
                ])
            }
        }
    };

    Ok(tokens.into())
}
