from setuptools import setup

setup(
    version = '0.0.1',
    name = 'untimed',
    description = 'System to solve temporals programs with special handling of temporal constraints.',
    author = 'Klaus Strauch',
    license = 'MIT',
    packages = ['untimed', 'untimed.propagator', 'untimed.theory'],
    test_suite = 'untimed.tests',
    zip_safe = False,
    entry_points = {
        'console_scripts': [
            'untimed=untimed:main',
        ]
    }
)