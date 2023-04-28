/*
 * Copyright (c) 2018 Demerzel Solutions Limited
 * This file is part of the Nethermind library.
 *
 * The Nethermind library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Nethermind library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Nethermind. If not, see <http://www.gnu.org/licenses/>.
 */

using System.Threading.Tasks;
using Nethermind.DataMarketplace.TestRunner.Framework;

namespace Nethermind.DataMarketplace.TestRunner.Tester.Steps
{
    public class KillProcessTestStep : TestStepBase
    {
        private readonly NethermindProcessWrapper _process;
        private readonly int _delay;

        public KillProcessTestStep(string name, NethermindProcessWrapper process,
            int delay = 0) : base(name)
        {
            _process = process;
            _delay = delay;
        }

        public override async Task<TestResult> ExecuteAsync()
        {
            _process.Kill();
            if (_delay > 0)
            {
                await Task.Delay(_delay);
            }

            return GetResult(!_process.IsRunning);
        }
    }
}