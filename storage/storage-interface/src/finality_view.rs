use std::sync::{Arc, RwLock};

use aptos_crypto::HashValue;
use aptos_types::{
    aggregate_signature::AggregateSignature,
    block_info::BlockInfo,
    ledger_info::{LedgerInfo, LedgerInfoWithSignatures},
    transaction::Version,
};

use crate::{AptosDbError, DbReader, Result};

/// A wrapper over [`DbReader`], representing ledger at the end of a block
/// as the latest ledger and its version as the latest transaction version.
pub struct FinalityView {
    reader: Arc<dyn DbReader>,
    finalized_ledger_info: RwLock<Option<LedgerInfoWithSignatures>>,
}

impl FinalityView {
    pub fn new(reader: Arc<dyn DbReader>) -> Self {
        Self {
            reader,
            finalized_ledger_info: RwLock::new(None),
        }
    }
}

impl FinalityView {
    /// Returns the height of the previously finalized block.
    ///
    /// If [`set_finalized_block_height`] has never been called on this
    /// instance, `None` is returned.
    pub fn finalized_block_height(&self) -> Option<u64> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        fin_ledger_info.as_ref().map(|ledger_info| ledger_info.commit_info().version())
    }

    /// Updates the information on the latest finalized block at the specified height.
    pub fn set_finalized_block_height(&self, height: u64) -> Result<()> {
        let (_start_ver, end_ver, block_event) = self.reader.get_block_info_by_height(height)?;
        let block_hash = block_event.hash()?;
        let block_info = BlockInfo::new(
            block_event.epoch(),
            block_event.round(),
            block_hash,
            self.reader.get_accumulator_root_hash(end_ver)?,
            end_ver,
            block_event.proposed_time(),
            None,
        );
        // FinalityView is created for Movement, where we don't use the consensus hash
        // or the ledger info signatures. So we leave them empty here and can still construct
        // a valid ledger info for the view.
        // In a more general implementation, this API could accept LedgerInfoWithSignatures
        // which is either preserved from an earlier version, or fudged like in our case.
        let ledger_info = LedgerInfo::new(block_info, HashValue::zero());
        let aggregate_signature = AggregateSignature::empty();
        let ledger_info = LedgerInfoWithSignatures::new(ledger_info, aggregate_signature);
        let mut fin_legder_info = self.finalized_ledger_info.write().unwrap();
        *fin_legder_info = Some(ledger_info);
        Ok(())
    }
}

impl DbReader for FinalityView {
    fn get_read_delegatee(&self) -> &dyn DbReader {
        &*self.reader
    }

    fn get_latest_ledger_info_option(&self) -> Result<Option<LedgerInfoWithSignatures>> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        Ok(fin_ledger_info.clone())
    }

    fn get_synced_version(&self) -> Result<Version> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        fin_ledger_info
            .as_ref()
            .map(|li| li.ledger_info().version())
            .ok_or_else(|| AptosDbError::NotFound("finalized version".into()))
    }

    fn get_latest_state_checkpoint_version(&self) -> Result<Option<Version>> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        let version = fin_ledger_info
            .as_ref()
            .map(|li| li.ledger_info().version());
        Ok(version)
    }

    // TODO: override any other methods needed to maintain the illusion.
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use aptos_crypto::HashValue;
    use aptos_types::state_store::{state_key::StateKey, TStateView as _};

    use super::*;
    use crate::{mock::MockDbReaderWriter, state_view::LatestDbStateCheckpointView as _};

    #[test]
    fn test_finalized_block_height() -> anyhow::Result<()> {
        let view = Arc::new(FinalityView::new(Arc::new(MockDbReaderWriter)));
        assert!(view.finalized_block_height().is_none());
        view.set_finalized_block_height(1)?;
        assert_eq!(view.finalized_block_height(), Some(1));
        Ok(())
    }

    #[test]
    fn test_get_latest_ledger_info() -> anyhow::Result<()> {
        // If the mock is changed to be stateful, this should be ref-counted
        // and shared with the view.
        let mock = MockDbReaderWriter;
        let view = FinalityView::new(Arc::new(MockDbReaderWriter));

        let ledger_info = view.get_latest_ledger_info_option()?;
        assert_eq!(ledger_info, None);
        let blockheight = 1;

        // Set the finalized ledger info
        view.set_finalized_block_height(blockheight)?;

        // Capture the block event once
        let (_start_ver, end_ver, block_event) =
            mock.get_block_info_by_height(blockheight)?;
        let block_hash = block_event.hash()?; // Used to verify hash is generated

        let block_info = BlockInfo::new(
            block_event.epoch(),
            block_event.round(),
            block_hash,
            HashValue::zero(),
            end_ver,
            block_event.proposed_time(),
            None,
        );
        let ledger_info = LedgerInfo::new(block_info, HashValue::zero());
        let expected_ledger_info =
            LedgerInfoWithSignatures::new(ledger_info, AggregateSignature::empty());

        // Get the latest ledger info after setting it
        let ledger_info = view.get_latest_ledger_info_option()?.unwrap();

        assert_eq!(ledger_info, expected_ledger_info);

        Ok(())
    }

    #[test]
    fn test_get_synced_version() -> anyhow::Result<()> {
        let view = FinalityView::new(Arc::new(MockDbReaderWriter));
        let res = view.get_synced_version();
        assert!(res.is_err());
        let blockheight = 1;
        view.set_finalized_block_height(blockheight)?;
        let version = view.get_synced_version()?;
        assert_eq!(version, 1);
        Ok(())
    }

    #[test]
    fn test_get_latest_state_checkpoint_version() -> Result<()> {
        let view = FinalityView::new(Arc::new(MockDbReaderWriter));
        let version = view.get_latest_state_checkpoint_version()?;
        assert_eq!(version, None);
        view.set_finalized_block_height(1)?;
        let version = view.get_latest_state_checkpoint_version()?;
        assert_eq!(version, Some(1));
        Ok(())
    }

    #[test]
    fn test_latest_state_checkpoint_view() -> anyhow::Result<()> {
        let view = Arc::new(FinalityView::new(Arc::new(MockDbReaderWriter)));
        let reader: Arc<dyn DbReader> = view.clone();
        view.set_finalized_block_height(1)?;
        let latest_state_view = reader.latest_state_checkpoint_view()?;
        // TODO: modify mock so we get different states for different versions
        let key = StateKey::raw(&[1]);
        let value = latest_state_view.get_state_value(&key)?.unwrap();
        assert_eq!(value.bytes(), &vec![1]);
        Ok(())
    }
}
