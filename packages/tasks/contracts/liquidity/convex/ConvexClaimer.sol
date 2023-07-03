// SPDX-License-Identifier: GPL-3.0-or-later
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

pragma solidity ^0.8.0;

import '@mimic-fi/v3-connectors/contracts/liquidity/convex/ConvexConnector.sol';

import './BaseConvexTask.sol';
import './interfaces/IConvexClaimer.sol';

/**
 * @title Convex claimer task
 */
contract ConvexClaimer is IConvexClaimer, BaseConvexTask {
    /**
     * @dev Convex claimer task config. Only used in the initializer.
     */
    struct ConvexConfig {
        BaseConvexConfig baseConvexConfig;
    }

    /**
     * @dev Initializes a Convex claimer task
     */
    function initialize(ConvexConfig memory config) external initializer {
        _initialize(config.baseConvexConfig);
    }

    /**
     * @dev Executes the Convex claimer task
     */
    function call(address pool)
        external
        override
        authP(authParams(pool))
        baseTaskCall(pool, 0) // Cannot know how much it will claim
    {
        bytes memory connectorData = abi.encodeWithSelector(ConvexConnector.claim.selector, pool);
        ISmartVault(smartVault).execute(connector, connectorData);
    }
}