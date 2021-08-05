// Copyright 2021 Parallel Finance Developer.
// This file is part of Parallel Finance.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Groups common pool related structures

use parallel_primitives::{Balance, CurrencyId};

use crate::amm_type::AmmType;

#[derive(
    Clone,
    PartialEq,
    parity_scale_codec::Decode,
    parity_scale_codec::Encode,
    sp_runtime::RuntimeDebug,
)]
pub struct Pool {
    pub amm_type: AmmType,
    pub base_amount: Balance,
    pub quote_amount: Balance,
    pub asset_base: CurrencyId,
    pub asset_quote: CurrencyId,
}

#[derive(
    Clone,
    PartialEq,
    parity_scale_codec::Decode,
    parity_scale_codec::Encode,
    sp_runtime::RuntimeDebug,
)]
pub struct LiquidityProviderAmounts {
    pub base_amount: Balance,
    pub quote_amount: Balance,
}

#[derive(
    Clone,
    PartialEq,
    parity_scale_codec::Decode,
    parity_scale_codec::Encode,
    sp_runtime::RuntimeDebug,
)]
pub enum SwapType {
    Buy,
    Sell,
}
