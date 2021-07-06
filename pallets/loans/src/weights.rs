// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Autogenerated weights for pallet_loans
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 3.0.0
//! DATE: 2021-06-09, STEPS: `[50, ]`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// ./target/release/parallel-dev
// benchmark
// --chain=dev
// --execution=wasm
// --wasm-execution=compiled
// --pallet=pallet_loans
// --extrinsic=*
// --steps=50
// --repeat=20
// --heap-pages=4096
// --template=./.maintain/frame-weight-template.hbs
// --output=./pallets/loans/src/weights.rs

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{
    traits::Get,
    weights::{constants::RocksDbWeight, Weight},
};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_loans.
pub trait WeightInfo {
    fn active_market() -> Weight;
    fn add_market() -> Weight;
    fn update_market() -> Weight;
    fn mint() -> Weight;
    fn borrow() -> Weight;
    fn redeem() -> Weight;
    fn redeem_all() -> Weight;
    fn repay_borrow() -> Weight;
    fn repay_borrow_all() -> Weight;
    fn transfer_token() -> Weight;
    fn collateral_asset() -> Weight;
    fn liquidate_borrow() -> Weight;
    fn add_reserves() -> Weight;
    fn reduce_reserves() -> Weight;
}

/// Weights for pallet_loans using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
    fn active_market() -> Weight {
        0
    }
    fn add_market() -> Weight {
        0
    }
    fn update_market() -> Weight {
        0
    }
    fn mint() -> Weight {
        (63_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(6 as Weight))
            .saturating_add(T::DbWeight::get().writes(5 as Weight))
    }
    fn borrow() -> Weight {
        (183_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(32 as Weight))
            .saturating_add(T::DbWeight::get().writes(6 as Weight))
    }
    fn redeem() -> Weight {
        (67_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(6 as Weight))
            .saturating_add(T::DbWeight::get().writes(5 as Weight))
    }
    fn redeem_all() -> Weight {
        (70_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(6 as Weight))
            .saturating_add(T::DbWeight::get().writes(5 as Weight))
    }
    fn repay_borrow() -> Weight {
        (60_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(5 as Weight))
            .saturating_add(T::DbWeight::get().writes(4 as Weight))
    }
    fn repay_borrow_all() -> Weight {
        (72_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(5 as Weight))
            .saturating_add(T::DbWeight::get().writes(4 as Weight))
    }
    fn transfer_token() -> Weight {
        (48_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(3 as Weight))
            .saturating_add(T::DbWeight::get().writes(3 as Weight))
    }
    fn collateral_asset() -> Weight {
        (26_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(2 as Weight))
            .saturating_add(T::DbWeight::get().writes(1 as Weight))
    }
    fn liquidate_borrow() -> Weight {
        (123_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(13 as Weight))
            .saturating_add(T::DbWeight::get().writes(6 as Weight))
    }
    fn add_reserves() -> Weight {
        (49_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(3 as Weight))
            .saturating_add(T::DbWeight::get().writes(3 as Weight))
    }
    fn reduce_reserves() -> Weight {
        (49_000_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(3 as Weight))
            .saturating_add(T::DbWeight::get().writes(3 as Weight))
    }
}

// For backwards compatibility and tests
impl WeightInfo for () {
    fn active_market() -> Weight {
        0
    }
    fn add_market() -> Weight {
        0
    }
    fn update_market() -> Weight {
        0
    }
    fn mint() -> Weight {
        (63_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(6 as Weight))
            .saturating_add(RocksDbWeight::get().writes(5 as Weight))
    }
    fn borrow() -> Weight {
        (183_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(32 as Weight))
            .saturating_add(RocksDbWeight::get().writes(6 as Weight))
    }
    fn redeem() -> Weight {
        (67_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(6 as Weight))
            .saturating_add(RocksDbWeight::get().writes(5 as Weight))
    }
    fn redeem_all() -> Weight {
        (70_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(6 as Weight))
            .saturating_add(RocksDbWeight::get().writes(5 as Weight))
    }
    fn repay_borrow() -> Weight {
        (60_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(5 as Weight))
            .saturating_add(RocksDbWeight::get().writes(4 as Weight))
    }
    fn repay_borrow_all() -> Weight {
        (72_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(5 as Weight))
            .saturating_add(RocksDbWeight::get().writes(4 as Weight))
    }
    fn transfer_token() -> Weight {
        (48_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(3 as Weight))
            .saturating_add(RocksDbWeight::get().writes(3 as Weight))
    }
    fn collateral_asset() -> Weight {
        (26_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(2 as Weight))
            .saturating_add(RocksDbWeight::get().writes(1 as Weight))
    }
    fn liquidate_borrow() -> Weight {
        (123_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(13 as Weight))
            .saturating_add(RocksDbWeight::get().writes(6 as Weight))
    }
    fn add_reserves() -> Weight {
        (49_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(3 as Weight))
            .saturating_add(RocksDbWeight::get().writes(3 as Weight))
    }
    fn reduce_reserves() -> Weight {
        (49_000_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(3 as Weight))
            .saturating_add(RocksDbWeight::get().writes(3 as Weight))
    }
}
