// What each mode of the demo asks for: its fields, the generator families behind «Random task», and hints.
// Plain data with no engine import, so the page draws the form before the engine has loaded; run.js solves.

const V = { key: 'v', label: 'Variable', placeholder: 'x', size: 'xs' };

export const NUMBER_OPS = [
    ['gcd', 'gcd', 'Two integers: 252, 198'],
    ['lcm', 'lcm', 'Two integers: 12, 18'],
    ['factor', 'prime factors', 'An integer: 360'],
    ['phi', 'Euler’s φ(n)', 'An integer: 36'],
    ['prime', 'is it prime? (Miller–Rabin)', 'An integer: 561'],
    ['modpow', 'aᵉ mod m', 'a, e, m: 3, 200, 7'],
    ['modinv', 'inverse mod m', 'a, m: 7, 26'],
    ['congruence', 'solve ax ≡ b (mod m)', 'a, b, m: 6, 4, 10'],
    ['diophantine', 'solve ax + by = c in integers', 'a, b, c: 12, 18, 30'],
    ['crt', 'Chinese remainder theorem', 'Remainders and moduli: 2 mod 3, 3 mod 5, 2 mod 7'],
    ['base', 'write in another base', 'A number and a base: 255, 2 or 0.1, 2'],
    ['cf', 'continued fraction', 'A fraction or a root: 415/93, sqrt(7)'],
    ['rsa', 'an RSA key from two primes', 'p, q: 61, 53'],
    ['divisibility', 'divisibility test', 'A number and a divisor (2, 3, 4, 5, 8, 9, 10, 11, 25, …): 123456, 11'],
];

export const MATRIX_OPS = [
    ['det', 'determinant'],
    ['inverse', 'inverse'],
    ['rref', 'row echelon form and rank'],
    ['eigen', 'eigenvalues'],
    ['diagonalize', 'diagonalisation'],
    ['solve', 'solve Ax = b'],
];

export const MODES = [
    {
        id: 'equation',
        label: 'Equations',
        fields: [
            { key: 'q', label: 'Equation', placeholder: 'x^2 - 5x + 6 = 0', main: true },
            V,
            { key: 'interval', label: 'Roots on', placeholder: '[0; 2pi]', size: 'sm' },
            { key: 'complex', label: 'Complex roots', type: 'check' },
        ],
        families: ['linear-eq', 'quadratic-eq', 'exp-eq', 'log-eq', 'radical-eq', 'rational-eq', 'abs-eq', 'trig-eq-interval'],
    },
    {
        id: 'inequality',
        label: 'Inequalities',
        fields: [{ key: 'q', label: 'Inequality', placeholder: '(x - 1)(x + 3)/(x - 5) >= 0', main: true }, V],
        families: ['linear-ineq', 'quad-ineq', 'rat-ineq', 'log-ineq', 'exp-ineq'],
    },
    {
        id: 'system',
        label: 'Systems',
        fields: [
            { key: 'q', label: 'Equations, one per line', placeholder: 'x + y = 3\nx - y = 1', main: true, lines: 3 },
            {
                key: 'method',
                label: 'Method',
                type: 'select',
                options: [
                    ['', 'automatic'],
                    ['substitution', 'substitution'],
                    ['addition', 'addition'],
                    ['cramer', 'Cramer’s rule'],
                    ['gauss', 'Gaussian elimination'],
                ],
            },
        ],
        families: ['linear-system', 'nonlinear-system'],
    },
    {
        id: 'parameter',
        label: 'Parameters',
        fields: [
            { key: 'q', label: 'Equation with a parameter', placeholder: 'x^2 - 2a x + a + 6 = 0', main: true },
            { key: 'param', label: 'Parameter', placeholder: 'a', size: 'xs' },
            {
                key: 'want',
                label: 'When are there',
                type: 'select',
                options: [
                    ['two-roots', 'two roots'],
                    ['one-root', 'one root'],
                    ['no-roots', 'no roots'],
                    ['has-roots', 'some roots'],
                    ['3', 'exactly 3 roots'],
                    ['4', 'exactly 4 roots'],
                ],
            },
        ],
        families: ['param-two-roots'],
    },
    {
        id: 'derivative',
        label: 'Derivatives',
        fields: [{ key: 'q', label: 'Function', placeholder: 'x^2 sin x', main: true }, V, { key: 'n', label: 'Order', placeholder: '1', size: 'xs' }],
        families: ['derivative'],
    },
    {
        id: 'integral',
        label: 'Integrals',
        fields: [
            { key: 'q', label: 'Integrand', placeholder: 'x cos x', main: true },
            V,
            { key: 'a', label: 'From', placeholder: 'optional', size: 'sm' },
            { key: 'b', label: 'To', placeholder: 'optional', size: 'sm' },
        ],
        families: ['antiderivative', 'definite-integral'],
        note: 'Give both limits for a definite integral; inf works too.',
    },
    {
        id: 'limit',
        label: 'Limits',
        fields: [
            { key: 'q', label: 'Function', placeholder: 'sin(3x)/x', main: true },
            V,
            { key: 'at', label: 'As it tends to', placeholder: '0', size: 'sm' },
            {
                key: 'side',
                label: 'Side',
                type: 'select',
                options: [
                    ['', 'both'],
                    ['left', 'left'],
                    ['right', 'right'],
                ],
            },
        ],
        families: ['limit'],
        note: 'The point may be a number, inf or -inf.',
    },
    {
        id: 'extremum',
        label: 'Extrema',
        fields: [
            { key: 'q', label: 'Function', placeholder: 'x^3 - 3x', main: true },
            V,
            { key: 'a', label: 'Segment from', placeholder: 'optional', size: 'sm' },
            { key: 'b', label: 'to', placeholder: 'optional', size: 'sm' },
            {
                key: 'kind',
                label: 'Find',
                type: 'select',
                options: [
                    ['max', 'the greatest value'],
                    ['min', 'the least value'],
                ],
            },
        ],
        families: ['extremum'],
        note: 'Leave the segment empty to find the points of maximum and minimum.',
    },
    {
        id: 'taylor',
        label: 'Taylor',
        fields: [
            { key: 'q', label: 'Function', placeholder: 'e^x', main: true },
            V,
            { key: 'at', label: 'Around', placeholder: '0', size: 'xs' },
            { key: 'n', label: 'Degree', placeholder: '4', size: 'xs' },
        ],
    },
    {
        id: 'ode',
        label: 'ODEs',
        fields: [{ key: 'q', label: 'Equation; initial conditions after ;', placeholder: "y'' + y = x; y(0) = 0; y'(0) = 0", main: true, noPreview: true }],
        families: ['ode'],
    },
    {
        id: 'series',
        label: 'Series',
        fields: [
            { key: 'q', label: 'Term', placeholder: '1/(k(k + 1))', main: true },
            { key: 'k', label: 'Index', placeholder: 'k', size: 'xs' },
            { key: 'a', label: 'From', placeholder: '1', size: 'xs' },
            { key: 'b', label: 'To', placeholder: 'inf', size: 'xs' },
        ],
        families: ['geometric-series'],
    },
    {
        id: 'value',
        label: 'Values',
        fields: [{ key: 'q', label: 'Expression', placeholder: '36^(log_6(5))', main: true }],
        families: ['log-value', 'power-value', 'trig-value'],
    },
    {
        id: 'algebra',
        label: 'Algebra',
        fields: [
            { key: 'q', label: 'Expression', placeholder: 'x^3 - 8', main: true },
            {
                key: 'op',
                label: 'Do',
                type: 'select',
                options: [
                    ['factor', 'factor'],
                    ['expand', 'expand'],
                    ['simplify', 'reduce the fraction'],
                ],
            },
        ],
        families: ['factor', 'reduce-fraction'],
    },
    {
        id: 'numbers',
        label: 'Number theory',
        fields: [
            { key: 'q', label: 'Numbers', placeholder: '252, 198', main: true, noPreview: true },
            { key: 'op', label: 'Find', type: 'select', options: NUMBER_OPS.map(([k, label]) => [k, label]) },
        ],
        hint: (f) => NUMBER_OPS.find(([k]) => k === (f.op || 'gcd'))?.[2],
    },
    {
        id: 'matrices',
        label: 'Matrices',
        fields: [
            { key: 'q', label: 'Matrix A, one row per line', placeholder: '2 1\n1 3', main: true, lines: 3, noPreview: true },
            { key: 'op', label: 'Find', type: 'select', options: MATRIX_OPS },
            { key: 'b', label: 'b, for Ax = b', placeholder: '3, 1', size: 'sm', when: (f) => f.op === 'solve' },
        ],
    },
];

export const MODE = Object.fromEntries(MODES.map((m) => [m.id, m]));
